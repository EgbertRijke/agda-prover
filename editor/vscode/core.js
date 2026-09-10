// Copyright (C) 2026 Egbert Rijke and contributors
// SPDX-License-Identifier: GPL-3.0-or-later
'use strict';

const fs = require('fs');
const os = require('os');
const path = require('path');

const SUPPORTED_SUFFIXES = Object.freeze(['.lagda.md', '.agda']);

const KNOWN_AGDA_RELOAD_ADAPTERS = Object.freeze([
  Object.freeze({extensionId: 'bdrisc.agda2-vscode', command: 'agda.load'}),
  Object.freeze({extensionId: 'banacorn.agda-mode', command: 'agda-mode.load'}),
  Object.freeze({extensionId: 'guilhermeespada.agda-mode-fork', command: 'agda-mode.load'}),
  Object.freeze({extensionId: 'stickypiston.avea', command: 'avea.load-file'})
]);

function isSupportedAgdaPath(filename) {
  if (typeof filename !== 'string') return false;
  return SUPPORTED_SUFFIXES.some(suffix => filename.endsWith(suffix));
}

function expandHome(value) {
  if (typeof value !== 'string' || value.length === 0) return value;
  if (value === '~') return os.homedir();
  if (value.startsWith(`~${path.sep}`)) {
    return path.join(os.homedir(), value.slice(2));
  }
  return value;
}

function normalizedPath(value) {
  const resolved = path.resolve(expandHome(value));
  try {
    return fs.realpathSync(resolved);
  } catch (_error) {
    return resolved;
  }
}

function isAgdaProverRoot(candidate) {
  if (!candidate) return false;
  return fs.existsSync(path.join(candidate, 'pyproject.toml')) &&
    fs.existsSync(path.join(candidate, 'src', 'agdaprover', '__main__.py'));
}

function ancestors(start) {
  const result = [];
  let current = normalizedPath(start);
  while (true) {
    result.push(current);
    const parent = path.dirname(current);
    if (parent === current) return result;
    current = parent;
  }
}

function resolveProjectRoot(options, predicate = isAgdaProverRoot) {
  // A standalone checkout is preferred. Also accept its containing workspace,
  // as used when developing the product as an agda-prover submodule.
  const productRoot = candidate => {
    if (predicate(candidate)) return candidate;
    const nested = path.join(candidate, 'agda-prover');
    return predicate(nested) ? normalizedPath(nested) : null;
  };
  const configuredRoot = options.configuredRoot || '';
  const environmentRoot = options.environmentRoot || '';
  const explicit = configuredRoot || environmentRoot;
  if (explicit) {
    const candidate = normalizedPath(explicit);
    const root = productRoot(candidate);
    return root
      ? {root, source: configuredRoot ? 'setting' : 'environment'}
      : {root: null, source: null, invalidExplicit: candidate};
  }

  const seeds = [];
  if (options.sourceFile) seeds.push(path.dirname(options.sourceFile));
  for (const folder of options.workspaceFolders || []) seeds.push(folder);
  if (options.extensionPath) {
    seeds.push(options.extensionPath);
    try {
      seeds.push(fs.realpathSync(options.extensionPath));
    } catch (_error) {
      // A non-existent development path is simply not a discovery candidate.
    }
  }

  const seen = new Set();
  for (const seed of seeds) {
    for (const candidate of ancestors(seed)) {
      if (seen.has(candidate)) continue;
      seen.add(candidate);
      const root = productRoot(candidate);
      if (root) return {root, source: 'discovered'};
    }
  }
  return {root: null, source: 'installed-cli'};
}

function buildBackend(options) {
  const sourceDirectory = options.sourceFile
    ? path.dirname(options.sourceFile)
    : process.cwd();
  const cwd = options.root || (options.workspaceFolders || [])[0] || sourceDirectory;
  if (options.executable) {
    return {
      command: expandHome(options.executable),
      prefixArgs: [],
      cwd,
      pythonPath: null,
      description: options.executable
    };
  }
  if (options.root) {
    const automaticPython = options.platform === 'win32' ? 'python' : 'python3';
    const python = options.pythonCommand && options.pythonCommand !== 'auto'
      ? expandHome(options.pythonCommand)
      : automaticPython;
    return {
      command: python,
      prefixArgs: ['-m', 'agdaprover'],
      cwd: options.root,
      pythonPath: path.join(options.root, 'src'),
      description: `${python} -m agdaprover (${options.root})`
    };
  }
  return {
    command: 'agdaprover',
    prefixArgs: [],
    cwd,
    pythonPath: null,
    description: 'agdaprover from PATH'
  };
}

function extensionId(extension) {
  return String(extension.id || '').toLowerCase();
}

function contributedCommands(extension) {
  const contributes = extension.packageJSON && extension.packageJSON.contributes;
  return contributes && Array.isArray(contributes.commands) ? contributes.commands : [];
}

function genericAgdaLoadCommands(extensions, available) {
  const commands = [];
  for (const extension of extensions) {
    const keywords = extension.packageJSON &&
      Array.isArray(extension.packageJSON.keywords)
      ? extension.packageJSON.keywords
      : [];
    const metadata = [
      extension.id,
      extension.packageJSON && extension.packageJSON.name,
      extension.packageJSON && extension.packageJSON.displayName,
      ...keywords
    ].join(' ').toLowerCase();
    if (!metadata.includes('agda')) continue;
    for (const contribution of contributedCommands(extension)) {
      const title = String(contribution.title || '').trim();
      const category = String(contribution.category || '').toLowerCase();
      const command = contribution.command;
      const loadTitle = /^load(?:\s+(?:an?\s+)?agda)?(?:\s+file)?$/i.test(title);
      if (typeof command === 'string' && loadTitle &&
          (category.includes('agda') || metadata.includes('agda')) &&
          available.has(command)) {
        commands.push(command);
      }
    }
  }
  return commands;
}

function selectAgdaReloadCommand(options) {
  const configured = options.configured || 'auto';
  if (configured === 'none') return null;
  const available = new Set(options.availableCommands || []);
  if (configured !== 'auto') return available.has(configured) ? configured : null;

  const extensions = options.extensions || [];
  const byId = new Map(extensions.map(extension => [extensionId(extension), extension]));
  for (const activeOnly of [true, false]) {
    for (const adapter of KNOWN_AGDA_RELOAD_ADAPTERS) {
      const extension = byId.get(adapter.extensionId);
      if (extension && (!activeOnly || extension.isActive) &&
          available.has(adapter.command)) {
        return adapter.command;
      }
    }
    const generic = genericAgdaLoadCommands(
      extensions.filter(extension => !activeOnly || extension.isActive),
      available
    );
    if (generic.length > 0) return generic[0];
  }

  for (const adapter of KNOWN_AGDA_RELOAD_ADAPTERS) {
    if (available.has(adapter.command)) return adapter.command;
  }
  return null;
}

function buildProjectConfiguration({executable = '', libraryFile = '', options = null, baseDirectory}) {
  if (typeof executable !== 'string' || typeof libraryFile !== 'string' ||
      (options !== null && (!Array.isArray(options) || options.some(value => typeof value !== 'string')))) {
    throw new Error('Invalid Agda checking configuration');
  }
  if (!executable && !libraryFile && options === null) return undefined;
  return {
    schema_version: 'agdaprover.project-configuration.v1',
    executable: executable && /[\\/]/.test(executable) && !executable.startsWith('~')
      ? path.resolve(baseDirectory, executable) : (executable || 'agda'),
    library_file: libraryFile ? path.resolve(baseDirectory, libraryFile) : null,
    options: options === null ? ['--without-K', '--exact-split'] : options
  };
}

module.exports = {
  KNOWN_AGDA_RELOAD_ADAPTERS,
  SUPPORTED_SUFFIXES,
  buildBackend,
  buildProjectConfiguration,
  isAgdaProverRoot,
  isSupportedAgdaPath,
  resolveProjectRoot,
  selectAgdaReloadCommand
};
