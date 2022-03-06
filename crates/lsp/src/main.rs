use std::collections::HashMap;

use anyhow::Result;
use crossbeam_channel::Sender;
use lsp_server::{Connection, Message, Notification, Request, RequestId, Response, ResponseError};
use lsp_types::{InitializeParams, ServerCapabilities};
use serde::Serialize;
use serde_json::Value;

fn main() -> Result<()> {
    let (connection, io_threads) = Connection::stdio();

    let server_capabilities = ServerCapabilities::default();
    let initialize_params = connection.initialize(serde_json::to_value(server_capabilities)?)?;
    let _initialize_params: InitializeParams = serde_json::from_value(initialize_params)?;

    let mut server = LspServer::new(connection.sender.clone());

    for message in &connection.receiver {
        match message {
            Message::Request(request) => {
                if connection.handle_shutdown(&request)? {
                    break;
                }
                server.handle_request(request);
            }
            Message::Response(response) => server.handle_response(response),
            Message::Notification(notification) => server.handle_notification(notification),
        }
    }

    io_threads.join()?;
    Ok(())
}

type ResponseHandler = Box<dyn FnOnce(Option<Value>, Option<ResponseError>)>;

struct LspServer {
    sender: Sender<Message>,
    requests: HashMap<RequestId, ResponseHandler>,
    next_id: i32,
}

impl LspServer {
    fn new(sender: Sender<Message>) -> Self {
        Self {
            sender,
            requests: HashMap::new(),
            next_id: 0,
        }
    }

    fn send_request<P: Serialize>(
        &mut self,
        method: String,
        params: P,
        handler: ResponseHandler,
    ) -> Result<()> {
        let id: RequestId = self.next_id.into();
        self.next_id += 1;
        self.sender.send(Message::Request(Request {
            id: id.clone(),
            method,
            params: serde_json::to_value(params)?,
        }))?;
        self.requests.insert(id, handler);
        Ok(())
    }

    fn handle_response(&mut self, response: Response) {
        if let Some(handler) = self.requests.remove(&response.id) {
            handler(response.result, response.error);
        }
    }

    fn handle_request(&mut self, request: Request) {
        todo!()
    }

    fn handle_notification(&mut self, notification: Notification) {
        todo!()
    }
}
