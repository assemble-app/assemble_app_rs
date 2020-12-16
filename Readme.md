# Assemble.app Rust Bindings

Bindings to deploy apps to Rust.

Currently implemnted:

* Database KV
* PubSub

## Building a View

Views should return an HTML string from the `render` method. This string can be constructed however you want, below we use the lightweight templating language, maude.

Events are dispatched by labeling elements with `assemble-` attributes. For example `<button assemble-click="i-was-clicked">Button</button>` Will call the `event` method of your `ViewHandler` and then the `render` method. `message` will be called whenever we recieve a message on the pubsub topic that we subscribe to on our `start` method. The `start` method gets called once when the page load and sets the initial state.

It is important that your `render` method finishes as fast as possible without making any extra calls. All platform functions are disabled during this method.


## Example Usage:

```
#[macro_use]
extern crate assemble_app;
#[macro_use]
extern crate serde;
#[macro_use]
extern crate maud;
use assemble_app::*;
use maud::html;

use serde::{Deserialize, Serialize};
use std::collections::HashMap;

assemble_init! {{
    register_view!(first_view, ViewHandler);
    register_call!(first_call, some_call);
}}

#[derive(Deserialize, Serialize)]
struct Input {
    inp: String,
}

#[derive(Deserialize, Serialize)]
struct Output {
    out: u32,
}

#[derive(Deserialize, Serialize)]
struct ViewHandler {
  clicks: u32,
  other_clicks: u32,
}

impl View for ViewHandler {
  fn start(_params: HashMap<String, String>) -> Result<Self> {
    pubsub_subscribe("clicks")?;
    Ok(ViewHandler { other_clicks: 0, clicks: 0 })
  }

  fn render(&self) -> Result<Html> {
    let markup = html! {
        div class="bg-indigo-700" {
          div class="max-w-2xl mx-auto text-center py-16 px-4 sm:py-20 sm:px-6 lg:px-8" {
            h2 class="text-3xl font-extrabold text-white sm:text-4xl" {
              span class="block" {
                "This page was completely written in rust"
              }
            }
            p class="mt-4 text-lg leading-6 text-indigo-200" {
              "Interact with other tabs by clicking the button below. View the source here: " a href="https://gist.github.com/hansonkd/237de86ab12eed770ebf9c2984bfaa8f" {
                github
              }
            }
            p class="mt-4 text-lg leading-6 text-indigo-200" {
              "Number of clicks from this tab: " (self.clicks)
            }
            p class="mt-4 text-lg leading-6 text-indigo-200" {
              "Number of clicks from other tabs and users: " (self.other_clicks)
            }
            button assemble-click="i-was-clicked" class="mt-8 w-full inline-flex items-center justify-center px-5 py-3 border border-transparent text-base font-medium rounded-md text-indigo-600 bg-white hover:bg-indigo-50 sm:w-auto" {
              "Click me"
            }
          }
        }
    };
    Ok(markup.into_string())
  }

  fn event(&mut self, msg: &str, payload: &[u8]) -> Result<()> {
    // These are clicks from the current user
    pubsub_publish_from("clicks", "click", "")?;
    self.clicks += 1;
    Ok(())
  }

  fn message(&mut self, topic: &str, event: &str, payload: &[u8]) -> Result<()> {
    // These are clicks from other users
    self.other_clicks += 1;
    Ok(())
  }
}

fn some_call(t: &Option<Input>) -> Result<Box<Output>> {
    let output = Output {
        out: 42,
    };
    Ok(Box::new(output))
}
```
