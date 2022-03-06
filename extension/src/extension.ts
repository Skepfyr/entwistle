import * as vscode from 'vscode';
import * as lc from 'vscode-languageclient/node';

let client: lc.LanguageClient;

export function activate(context: vscode.ExtensionContext) {
	let disposable = vscode.commands.registerCommand('entwistle.restart', async () => {
		vscode.window.showInformationMessage('Restarting Entwistle Language Server.');
		await client.stop();
		client.start();
		vscode.window.showInformationMessage('Restarted Entwistle Language Server.');
	});

	context.subscriptions.push(disposable);

	const run: lc.Executable = {
		command: '',
	};
	const serverOptions: lc.ServerOptions = {
		run,
		debug: run,
	};

	const clientOptions: lc.LanguageClientOptions = {
		documentSelector: [{ scheme: 'file', language: 'entwistle' }]
	};

	client = new lc.LanguageClient('entwistle', 'Entwistle Language Server', serverOptions, clientOptions);

	client.start();
}

export function deactivate(): Thenable<void> | undefined {
	if (client) {
		return client.stop();
	}
	return undefined;
}
