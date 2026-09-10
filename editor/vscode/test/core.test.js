'use strict';

const assert = require('node:assert/strict');
const fs = require('node:fs');
const os = require('node:os');
const path = require('node:path');
const test = require('node:test');

const core = require('../core');

test('bundled NNUE is the editor default with independent optional overrides', () => {
  const settings = require('../package.json').contributes.configuration.properties;
  assert.equal(settings['agdaprover.ranker'].default, 'nnue');
  for (const name of ['model', 'stepModel', 'actionModel']) {
    assert.equal(settings[`agdaprover.${name}`].default, '');
  }
  for (const operation of ['prove', 'prove-prefix', 'step']) {
    assert.deepEqual(core.modelsForOperation({ranker: 'nnue'}, operation),
      {model: null, actionModel: null});
  }
  const custom = {ranker: 'nnue', model: '/proof', stepModel: '/step', actionModel: '/or'};
  assert.deepEqual(core.modelsForOperation(custom, 'step'), {model: '/step', actionModel: null});
  assert.deepEqual(core.modelsForOperation(custom, 'prove-prefix'), {model: '/proof', actionModel: '/or'});
  assert.deepEqual(core.modelsForOperation({...custom, ranker: 'symbolic'}, 'prove-prefix'),
    {model: null, actionModel: null});
});

test('deep search delegates preset defaults and preserves explicit action limits', () => {
  assert.deepEqual(core.searchRequestOptions({}), {});
  assert.deepEqual(core.searchRequestOptions({searchProfile: 'deep', maxCandidates: null}),
    {search_profile: 'deep'});
  assert.deepEqual(core.searchRequestOptions({searchProfile: 'deep', maxCandidates: 17}),
    {search_profile: 'deep', max_candidates: 17});
  assert.throws(() => core.searchRequestOptions({searchProfile: 'unlimited'}), /Unknown/);
  assert.throws(() => core.searchRequestOptions({searchProfile: null}), /Unknown/);
  for (const invalid of [0, -1, true, '17', 1.5]) {
    assert.throws(() => core.searchRequestOptions({maxCandidates: invalid}), /positive integer/);
  }
});

test('explicit project settings preserve defaults and empty option lists', () => {
  assert.equal(core.buildProjectConfiguration({baseDirectory: '/workspace'}), undefined);
  const configured = core.buildProjectConfiguration({libraryFile: 'libraries', options: [], baseDirectory: '/workspace'});
  assert.equal(configured.library_file, path.resolve('/workspace', 'libraries'));
  assert.deepEqual(configured.options, []);
  assert.equal(configured.schema_version, 'agdaprover.project-configuration.v1');
  assert.deepEqual(core.buildProjectConfiguration({executable: 'custom-agda', baseDirectory: '/workspace'}).options,
    ['--without-K', '--exact-split']);
  assert.equal(core.buildProjectConfiguration({executable: './bin/agda', baseDirectory: '/workspace'}).executable,
    path.resolve('/workspace', 'bin/agda'));
  assert.throws(() => core.buildProjectConfiguration({options: '--safe'}), /Invalid Agda/);
});

function makeRoot() {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), 'agdaprover-vscode-'));
  fs.mkdirSync(path.join(root, 'src', 'agdaprover'), {recursive: true});
  fs.writeFileSync(path.join(root, 'pyproject.toml'), '[project]\nname="agdaprover"\n');
  fs.writeFileSync(path.join(root, 'src', 'agdaprover', '__main__.py'), '');
  return root;
}

test('recognizes supported Agda files independently of language id', () => {
  assert.equal(core.isSupportedAgdaPath('/tmp/Example.agda'), true);
  assert.equal(core.isSupportedAgdaPath('/tmp/Example.lagda.md'), true);
  assert.equal(core.isSupportedAgdaPath('/tmp/Example.AGDA'), false);
  assert.equal(core.isSupportedAgdaPath('/tmp/Example.lagda.tex'), false);
  assert.equal(core.isSupportedAgdaPath('/tmp/Example.md'), false);
});

test('discovers a checkout from the source tree without configuration', t => {
  const root = makeRoot();
  const canonicalRoot = fs.realpathSync(root);
  t.after(() => fs.rmSync(root, {recursive: true, force: true}));
  const source = path.join(root, 'examples', 'Example.agda');
  fs.mkdirSync(path.dirname(source), {recursive: true});
  fs.writeFileSync(source, 'module Example where\n');
  assert.deepEqual(core.resolveProjectRoot({sourceFile: source}), {
    root: canonicalRoot,
    source: 'discovered'
  });
});

test('discovers the checkout containing the extension itself', () => {
  const expected = fs.realpathSync(path.join(__dirname, '..', '..', '..'));
  assert.deepEqual(core.resolveProjectRoot({
    extensionPath: path.join(__dirname, '..')
  }), {
    root: expected,
    source: 'discovered'
  });
});

test('reports an invalid explicit checkout instead of silently guessing', t => {
  const directory = fs.mkdtempSync(path.join(os.tmpdir(), 'agdaprover-invalid-'));
  const canonicalDirectory = fs.realpathSync(directory);
  t.after(() => fs.rmSync(directory, {recursive: true, force: true}));
  assert.deepEqual(core.resolveProjectRoot({configuredRoot: directory}), {
    root: null,
    source: null,
    invalidExplicit: canonicalDirectory
  });
});

test('discovers a product submodule from a containing workspace or old setting', t => {
  const workspace = fs.mkdtempSync(path.join(os.tmpdir(), 'agdaprover-workspace-'));
  t.after(() => fs.rmSync(workspace, {recursive: true, force: true}));
  const root = path.join(workspace, 'agda-prover');
  fs.mkdirSync(path.join(root, 'src', 'agdaprover'), {recursive: true});
  fs.writeFileSync(path.join(root, 'pyproject.toml'), '[project]\nname="agda-prover"\n');
  fs.writeFileSync(path.join(root, 'src', 'agdaprover', '__main__.py'), '');
  const canonicalRoot = fs.realpathSync(root);
  assert.deepEqual(core.resolveProjectRoot({workspaceFolders: [workspace]}), {
    root: canonicalRoot, source: 'discovered'
  });
  assert.deepEqual(core.resolveProjectRoot({configuredRoot: workspace}), {
    root: canonicalRoot, source: 'setting'
  });
  assert.deepEqual(core.resolveProjectRoot({environmentRoot: workspace}), {
    root: canonicalRoot, source: 'environment'
  });
  assert.deepEqual(core.resolveProjectRoot({configuredRoot: root}), {
    root: canonicalRoot, source: 'setting'
  });
});

test('uses the repository module or installed CLI with no shell', () => {
  const local = core.buildBackend({
    root: '/checkout',
    pythonCommand: 'auto',
    platform: 'darwin',
    sourceFile: '/project/Example.agda'
  });
  assert.equal(local.command, 'python3');
  assert.deepEqual(local.prefixArgs, ['-m', 'agdaprover']);
  assert.equal(local.pythonPath, path.join('/checkout', 'src'));

  const installed = core.buildBackend({
    root: null,
    sourceFile: '/project/Example.agda',
    workspaceFolders: ['/project']
  });
  assert.equal(installed.command, 'agdaprover');
  assert.deepEqual(installed.prefixArgs, []);
  assert.equal(installed.cwd, '/project');
});

test('selects the active known Agda extension reload command', () => {
  const command = core.selectAgdaReloadCommand({
    configured: 'auto',
    availableCommands: ['agda.load', 'agda-mode.load'],
    extensions: [
      {id: 'bdrisc.agda2-vscode', isActive: false, packageJSON: {}},
      {id: 'banacorn.agda-mode', isActive: true, packageJSON: {}}
    ]
  });
  assert.equal(command, 'agda-mode.load');
});

test('supports Avea, future contributed load commands, explicit choice, and none', () => {
  assert.equal(core.selectAgdaReloadCommand({
    availableCommands: ['avea.load-file'],
    extensions: [{id: 'stickypiston.avea', isActive: true, packageJSON: {}}]
  }), 'avea.load-file');

  const future = {
    id: 'example.future-agda',
    isActive: true,
    packageJSON: {
      displayName: 'Future Agda',
      contributes: {commands: [{command: 'future.load', title: 'Load file', category: 'Agda'}]}
    }
  };
  assert.equal(core.selectAgdaReloadCommand({
    availableCommands: ['future.load'],
    extensions: [future]
  }), 'future.load');
  assert.equal(core.selectAgdaReloadCommand({
    configured: 'custom.load',
    availableCommands: ['custom.load']
  }), 'custom.load');
  assert.equal(core.selectAgdaReloadCommand({
    configured: 'missing.load',
    availableCommands: []
  }), null);
  assert.equal(core.selectAgdaReloadCommand({configured: 'none'}), null);

  assert.doesNotThrow(() => core.selectAgdaReloadCommand({
    availableCommands: [],
    extensions: [{
      id: 'example.malformed-agda-metadata',
      packageJSON: {keywords: 'agda'}
    }]
  }));
});

test('manifest has no Agda-extension dependency and activates extension-neutrally', () => {
  const manifest = JSON.parse(fs.readFileSync(path.join(__dirname, '..', 'package.json')));
  assert.equal(Object.hasOwn(manifest, 'extensionDependencies'), false);
  assert.ok(manifest.activationEvents.includes('onStartupFinished'));
  assert.equal(manifest.capabilities.untrustedWorkspaces.supported, false);
  assert.equal(manifest.capabilities.virtualWorkspaces.supported, false);
});

test('keybindings support direct chords and Agda2 state without excluding companions', () => {
  const manifest = JSON.parse(fs.readFileSync(path.join(__dirname, '..', 'package.json')));
  const bindings = manifest.contributes.keybindings;
  assert.ok(bindings.some(binding =>
    binding.command === 'agdaprover.proveDeep' && binding.key === 'ctrl+c ctrl+x ctrl+d'
  ));
  assert.ok(bindings.some(binding =>
    binding.command === 'agdaprover.proveDeep' && binding.key === 'ctrl+d' &&
    binding.when.includes("agda.keySequence == 'cc-x'")
  ));
  assert.ok(bindings.some(binding =>
    binding.command === 'agdaprover.provePrefix' &&
    binding.key === 'ctrl+c ctrl+x ctrl+p'
  ));
  assert.ok(bindings.some(binding =>
    binding.command === 'agdaprover.provePrefix' &&
    binding.key === 'ctrl+p' &&
    binding.when.includes("agda.keySequence == 'cc-x'")
  ));

  const recommendations = JSON.parse(fs.readFileSync(
    path.join(__dirname, '..', '..', '..', '.vscode', 'extensions.json')
  ));
  assert.ok(recommendations.recommendations.includes('bdrisc.agda2-vscode'));
  assert.equal(Object.hasOwn(recommendations, 'unwantedRecommendations'), false);

  const launch = JSON.parse(fs.readFileSync(
    path.join(__dirname, '..', '..', '..', '.vscode', 'launch.json')
  ));
  const args = launch.configurations[0].args;
  assert.ok(args.includes('${workspaceFolder}'));
  assert.equal(args.some(argument => argument.startsWith('--disable-extension=')), false);
});
