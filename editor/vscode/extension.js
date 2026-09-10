// Copyright (C) 2026 Egbert Rijke and contributors, including Emily Riehl
// SPDX-License-Identifier: GPL-3.0-or-later
'use strict';

const crypto = require('crypto');
const fs = require('fs');
const path = require('path');
const { spawn } = require('child_process');
const vscode = require('vscode');
const {
  buildBackend,
  buildProjectConfiguration,
  isSupportedAgdaPath,
  resolveProjectRoot,
  searchRequestOptions,
  selectAgdaReloadCommand
} = require('./core');

const MAX_OUTPUT_BYTES = 32 * 1024 * 1024;
const MAX_ERROR_BYTES = 1024 * 1024;
const SETUP_TIMEOUT_MS = 15_000;

let activeProcess = null;
let statusItem = null;

async function resetAgdaKeySequence() {
  await vscode.commands.executeCommand('agda.keySequence.escape')
    .then(undefined, () => undefined);
}

function workspaceFolderPaths(document) {
  const folders = [];
  const owner = document && vscode.workspace.getWorkspaceFolder(document.uri);
  if (owner && owner.uri.scheme === 'file') folders.push(owner.uri.fsPath);
  for (const folder of vscode.workspace.workspaceFolders || []) {
    if (folder.uri.scheme === 'file' && !folders.includes(folder.uri.fsPath)) {
      folders.push(folder.uri.fsPath);
    }
  }
  return folders;
}

function configuration(context, document) {
  const settings = vscode.workspace.getConfiguration('agdaprover', document && document.uri);
  const workspaceFolders = workspaceFolderPaths(document);
  const rootResolution = resolveProjectRoot({
    configuredRoot: settings.get('projectRoot', ''),
    environmentRoot: process.env.AGDAPROVER_PROJECT_ROOT || '',
    sourceFile: document && document.fileName,
    workspaceFolders,
    extensionPath: context.extensionPath
  });
  if (rootResolution.invalidExplicit) {
    throw new Error(
      `AgdaProver project root is not a checkout: ${rootResolution.invalidExplicit}`
    );
  }
  const backend = buildBackend({
    root: rootResolution.root,
    pythonCommand: settings.get('pythonCommand', 'auto'),
    executable: settings.get('executable', ''),
    sourceFile: document && document.fileName,
    workspaceFolders,
    platform: process.platform
  });
  return {
    backend,
    rootResolution,
    ranker: settings.get('ranker', 'symbolic'),
    model: settings.get('model', '') || null,
    stepModel: settings.get('stepModel', '') || null,
    actionModel: settings.get('actionModel', '') || null,
    reloadCommand: settings.get('reloadCommand', 'auto'),
    searchProfile: settings.get('searchProfile', 'standard'),
    maxCandidates: settings.get('maxCandidates', null),
    maxTermSize: settings.get('maxTermSize', 8),
    maxDepth: settings.get('maxDepth', null),
    timeoutSeconds: settings.get('timeoutSeconds', null),
    projectConfiguration: buildProjectConfiguration({
      executable: settings.get('agdaExecutable', ''),
      libraryFile: settings.get('libraryFile', ''),
      options: settings.get('agdaOptions', null),
      baseDirectory: workspaceFolders[0] || (document ? path.dirname(document.fileName) : context.extensionPath)
    })
  };
}

function digestFile(filename) {
  return crypto.createHash('sha256').update(fs.readFileSync(filename)).digest('hex');
}

function modelsForOperation(config, operation) {
  if (config.ranker !== 'nnue') {
    return {model: null, actionModel: null};
  }
  if (operation === 'step') {
    return {
      model: config.stepModel,
      actionModel: null
    };
  }
  return {
    model: config.model,
    actionModel: config.actionModel
  };
}

function isSupportedDocument(document) {
  return Boolean(document && document.uri.scheme === 'file' &&
    isSupportedAgdaPath(document.fileName));
}

function offsetRange(document, sourceRange) {
  if (!Array.isArray(sourceRange) || sourceRange.length !== 2) {
    throw new Error('AgdaProver returned a malformed source range');
  }
  return new vscode.Range(
    document.positionAt(sourceRange[0] - 1),
    document.positionAt(sourceRange[1] - 1)
  );
}

async function reloadWithCompanionExtension(config, document) {
  const activeEditor = vscode.window.activeTextEditor;
  if (!activeEditor || activeEditor.document.uri.toString() !== document.uri.toString()) {
    return null;
  }
  const availableCommands = await vscode.commands.getCommands(true);
  const command = selectAgdaReloadCommand({
    configured: config.reloadCommand,
    availableCommands,
    extensions: vscode.extensions.all
  });
  if (!command) {
    if (!['auto', 'none'].includes(config.reloadCommand)) {
      vscode.window.showWarningMessage(
        `Configured Agda reload command is unavailable: ${config.reloadCommand}`
      );
    }
    return null;
  }
  try {
    await vscode.commands.executeCommand(command);
    return command;
  } catch (error) {
    console.warn(`AgdaProver could not invoke ${command}: ${error.message}`);
    return null;
  }
}

async function applyEdit(document, edit, config) {
  if (!edit || edit.schema_version !== 'agdaprover.reconstruction.p0.v1') {
    throw new Error('AgdaProver returned an unsupported reconstruction');
  }
  const range = offsetRange(document, edit.source_range);
  if (document.getText(range) !== edit.original) {
    throw new Error('The source changed; refusing a stale AgdaProver edit');
  }
  const workspaceEdit = new vscode.WorkspaceEdit();
  workspaceEdit.replace(document.uri, range, edit.replacement);
  if (!await vscode.workspace.applyEdit(workspaceEdit)) {
    throw new Error('VS Code refused the AgdaProver edit');
  }
  if (!await document.save()) {
    throw new Error('VS Code could not save the AgdaProver edit');
  }
  await reloadWithCompanionExtension(config, document);
}

function resultDiagnostic(result) {
  const structured = result.diagnostics && result.diagnostics[0];
  return (structured && structured.message) || result.diagnostic || null;
}

async function applyResult(document, operation, result, config) {
  if (operation === 'step') {
    if (result.status !== 'accepted-step' || !result.action) {
      throw new Error(resultDiagnostic(result) || `AgdaProver step: ${result.status}`);
    }
    if (result.action.source_edit) {
      await applyEdit(document, result.action.source_edit, config);
      return;
    }
    const expression = result.action.expression;
    const goal = result.goal;
    if (typeof expression !== 'string' || !goal) {
      throw new Error('AgdaProver returned a malformed step');
    }
    await applyEdit(document, {
      schema_version: 'agdaprover.reconstruction.p0.v1',
      source_range: goal.source_range,
      original: document.getText(offsetRange(document, goal.source_range)),
      replacement: expression
    }, config);
    return;
  }
  if (result.status !== 'verified') {
    throw new Error(resultDiagnostic(result) || `AgdaProver: ${result.status}`);
  }
  if (!result.validation || !result.validation.checked || !result.trust_report) {
    throw new Error('AgdaProver result lacks fresh validation evidence');
  }
  await applyEdit(document, result.patch, config);
}

function processEnvironment(backend) {
  const environment = {...process.env};
  if (backend.pythonPath) {
    environment.PYTHONPATH = environment.PYTHONPATH
      ? `${backend.pythonPath}${path.delimiter}${environment.PYTHONPATH}`
      : backend.pythonPath;
  }
  return environment;
}

function startError(backend, error) {
  if (error && error.code === 'ENOENT') {
    return new Error(
      `Could not start ${backend.description}. Run “AgdaProver: Check Setup”, ` +
      'install the agdaprover CLI, or configure agdaprover.projectRoot.'
    );
  }
  return error instanceof Error ? error : new Error(String(error));
}

function runEditorAPI(config, operation, document, goalPosition, token) {
  const models = modelsForOperation(config, operation);
  const requestId = `vscode:${process.pid}:${Date.now()}`;
  const request = {
    schema_version: 'agdaprover.editor.request.v1',
    request_id: requestId,
    operation,
    source_file: document.fileName,
    source_sha256: digestFile(document.fileName),
    goal_position: goalPosition,
    ranker: config.ranker,
    model: models.model,
    action_model: models.actionModel,
    ...searchRequestOptions(config),
    max_term_size: config.maxTermSize,
    max_depth: config.maxDepth,
    timeout_seconds: config.timeoutSeconds
  };
  if (config.projectConfiguration) request.project_configuration = config.projectConfiguration;
  const backend = config.backend;
  return new Promise((resolve, reject) => {
    const child = spawn(
      backend.command,
      [...backend.prefixArgs, 'editor-api'],
      {
        cwd: backend.cwd,
        env: processEnvironment(backend),
        shell: false,
        stdio: ['pipe', 'pipe', 'pipe']
      }
    );
    activeProcess = child;
    let output = '';
    let errors = '';
    let outputOverflow = false;
    let settled = false;
    const cancellation = token.onCancellationRequested(() => child.kill('SIGTERM'));

    const fail = error => {
      if (settled) return;
      settled = true;
      cancellation.dispose();
      if (activeProcess === child) activeProcess = null;
      reject(startError(backend, error));
    };

    child.stdout.setEncoding('utf8');
    child.stderr.setEncoding('utf8');
    child.stdout.on('data', data => {
      output += data;
      if (Buffer.byteLength(output, 'utf8') > MAX_OUTPUT_BYTES) {
        outputOverflow = true;
        child.kill('SIGTERM');
      }
    });
    child.stderr.on('data', data => {
      if (Buffer.byteLength(errors, 'utf8') < MAX_ERROR_BYTES) errors += data;
    });
    child.stdin.on('error', () => {});
    child.on('error', fail);
    child.on('close', (code, signal) => {
      if (settled) return;
      cancellation.dispose();
      if (activeProcess === child) activeProcess = null;
      try {
        if (token.isCancellationRequested) throw new Error('AgdaProver was cancelled.');
        if (outputOverflow) throw new Error('AgdaProver exceeded the editor output limit.');
        if (!output) {
          throw new Error(
            `AgdaProver exited without a response (${signal || `status ${code}`}).` +
            (errors ? `\n${errors}` : '')
          );
        }
        const envelope = JSON.parse(output);
        if (envelope.schema_version !== 'agdaprover.editor.response.v1' ||
            envelope.request_id !== requestId) {
          throw new Error('AgdaProver returned a mismatched editor response');
        }
        if (document.isDirty || digestFile(document.fileName) !== request.source_sha256) {
          throw new Error('The source changed while AgdaProver was running');
        }
        settled = true;
        resolve(envelope.result);
      } catch (error) {
        fail(new Error(`${error.message}${errors && output ? `\n${errors}` : ''}`));
      }
    });
    child.stdin.end(`${JSON.stringify(request)}\n`);
  });
}

function checkBackend(config) {
  const backend = config.backend;
  return new Promise((resolve, reject) => {
    const child = spawn(
      backend.command,
      [...backend.prefixArgs, 'doctor', '--offline-audit'],
      {
        cwd: backend.cwd,
        env: processEnvironment(backend),
        shell: false,
        stdio: ['ignore', 'ignore', 'pipe']
      }
    );
    activeProcess = child;
    let errors = '';
    let timedOut = false;
    let settled = false;
    const timer = setTimeout(() => {
      timedOut = true;
      child.kill('SIGTERM');
    }, SETUP_TIMEOUT_MS);
    const finish = error => {
      if (settled) return;
      settled = true;
      clearTimeout(timer);
      if (activeProcess === child) activeProcess = null;
      error ? reject(startError(backend, error)) : resolve();
    };
    child.stderr.setEncoding('utf8');
    child.stderr.on('data', data => {
      if (Buffer.byteLength(errors, 'utf8') < MAX_ERROR_BYTES) errors += data;
    });
    child.on('error', finish);
    child.on('close', code => {
      if (timedOut) {
        finish(new Error('AgdaProver setup check timed out.'));
      } else if (code !== 0) {
        finish(new Error(errors || `AgdaProver setup check exited with status ${code}.`));
      } else {
        finish(null);
      }
    });
  });
}

async function showActionableError(error) {
  const action = await vscode.window.showErrorMessage(
    error.message || String(error),
    'Check Setup',
    'Open Settings'
  );
  if (action === 'Check Setup') {
    await vscode.commands.executeCommand('agdaprover.checkSetup');
  } else if (action === 'Open Settings') {
    await vscode.commands.executeCommand(
      'workbench.action.openSettings',
      '@ext:agdaprover.agdaprover'
    );
  }
}

async function execute(context, operation, searchProfile) {
  await resetAgdaKeySequence();
  const editor = vscode.window.activeTextEditor;
  if (!vscode.workspace.isTrusted) {
    vscode.window.showErrorMessage('Trust this workspace before running AgdaProver.');
    return;
  }
  if (!editor || !isSupportedDocument(editor.document)) {
    vscode.window.showErrorMessage('Open a local .agda or .lagda.md source first.');
    return;
  }
  if (activeProcess) {
    vscode.window.showErrorMessage('AgdaProver is already running.');
    return;
  }
  if (!await editor.document.save()) {
    vscode.window.showErrorMessage('Save the Agda source before running AgdaProver.');
    return;
  }
  try {
    const config = configuration(context, editor.document);
    if (searchProfile) config.searchProfile = searchProfile;
    const position = editor.document.offsetAt(editor.selection.active) + 1;
    const result = await vscode.window.withProgress({
      location: vscode.ProgressLocation.Notification,
      title: operation === 'step'
        ? 'AgdaProver: choosing a step'
        : `AgdaProver: ${config.searchProfile === 'deep' ? 'deep search for' : 'proving'} selected goals`,
      cancellable: true
    }, (_progress, token) => runEditorAPI(
      config,
      operation,
      editor.document,
      position,
      token
    ));
    await applyResult(editor.document, operation, result, config);
  } catch (error) {
    await showActionableError(error);
  }
}

async function checkSetup(context) {
  if (!vscode.workspace.isTrusted) {
    vscode.window.showErrorMessage('Trust this workspace before checking AgdaProver.');
    return;
  }
  if (activeProcess) {
    vscode.window.showErrorMessage('AgdaProver is already running.');
    return;
  }
  try {
    const editor = vscode.window.activeTextEditor;
    const document = editor && isSupportedDocument(editor.document)
      ? editor.document
      : null;
    const config = configuration(context, document);
    await checkBackend(config);
    const availableCommands = await vscode.commands.getCommands(true);
    const reload = selectAgdaReloadCommand({
      configured: config.reloadCommand,
      availableCommands,
      extensions: vscode.extensions.all
    });
    if (!reload && !['auto', 'none'].includes(config.reloadCommand)) {
      throw new Error(
        `Configured Agda reload command is unavailable: ${config.reloadCommand}`
      );
    }
    const reloadDescription = reload
      ? ` Companion reload: ${reload}.`
      : ' No companion Agda reload command is required or configured.';
    vscode.window.showInformationMessage(
      `AgdaProver is ready via ${config.backend.description}.${reloadDescription}`
    );
  } catch (error) {
    await showActionableError(error);
  }
}

function updateEditorContext(editor) {
  const supported = Boolean(editor && isSupportedDocument(editor.document));
  vscode.commands.executeCommand('setContext', 'agdaprover.supportedDocument', supported);
  if (!statusItem) return;
  if (supported) {
    statusItem.show();
  } else {
    statusItem.hide();
  }
}

function activate(context) {
  statusItem = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Right, 100);
  statusItem.name = 'AgdaProver';
  statusItem.text = '$(beaker) AgdaProver';
  statusItem.tooltip = 'Prove through the current goal, or all goals outside a hole';
  statusItem.command = 'agdaprover.provePrefix';

  context.subscriptions.push(
    statusItem,
    vscode.window.onDidChangeActiveTextEditor(updateEditorContext),
    vscode.commands.registerCommand(
      'agdaprover.provePrefix',
      () => execute(context, 'prove-prefix')
    ),
    vscode.commands.registerCommand(
      'agdaprover.proveDeep',
      () => execute(context, 'prove-prefix', 'deep')
    ),
    vscode.commands.registerCommand('agdaprover.step', () => execute(context, 'step')),
    vscode.commands.registerCommand('agdaprover.checkSetup', () => checkSetup(context)),
    vscode.commands.registerCommand('agdaprover.cancel', async () => {
      await resetAgdaKeySequence();
      if (activeProcess) activeProcess.kill('SIGTERM');
    })
  );
  updateEditorContext(vscode.window.activeTextEditor);
}

function deactivate() {
  if (activeProcess) activeProcess.kill('SIGTERM');
}

module.exports = {activate, deactivate};
