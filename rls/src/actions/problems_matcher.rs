use crate::actions::{
    diagnostics::{Diagnostic, Suggestion},
    InitActionContext,
};
use lazy_static::*;
use regex::Regex;
use rls_vfs::FileContents;
use std::fmt::Display;
use std::path::Path;

fn position_to_offset(text: &str, position: lsp_types::Position) -> Option<usize> {
    let mut line = 0;
    let mut offset_in_line = 0;
    for (count, character) in text.chars().enumerate() {
        if line == position.line && offset_in_line == position.character {
            return Some(count);
        }
        if character == '\n' {
            line += 1;
            offset_in_line = 0;
        } else {
            offset_in_line += 1;
        }
    }
    None
}

fn offset_to_position(text: &str, offset: usize) -> Option<lsp_types::Position> {
    let mut line = 0;
    let mut offset_in_line = 0;
    for (count, character) in text.chars().enumerate() {
        if count == offset {
            return Some(lsp_types::Position { line, character: offset_in_line });
        }
        if character == '\n' {
            line += 1;
            offset_in_line = 0;
        } else {
            offset_in_line += 1;
        }
    }
    None
}

#[derive(Copy, Clone, PartialEq)]
enum Whereable<'a> {
    Function(&'a str),
    Trait(&'a str),
    Implementation(Option<&'a str>, &'a str),
    Structure(&'a str),
    Enumeration(&'a str),
}

impl<'a> Display for Whereable<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            Whereable::Function(name) => write!(f, "function {}", name),
            Whereable::Trait(name) => write!(f, "trait {}", name),
            Whereable::Enumeration(name) => write!(f, "enumeration {}", name),
            Whereable::Structure(name) => write!(f, "structure {}", name),
            Whereable::Implementation(Some(trait_name), name) => {
                write!(f, "impl {} for {}", trait_name, name)
            }
            Whereable::Implementation(None, name) => write!(f, "impl {}", name),
        }
    }
}

#[derive(Copy, Clone, PartialEq)]
enum ScopeType<'a> {
    Unnamed,
    Whereable(Whereable<'a>),
}

impl<'a> Display for ScopeType<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            ScopeType::Unnamed => write!(f, "Unnamed Scope"),
            ScopeType::Whereable(whereable) => whereable.fmt(f),
        }
    }
}

impl<'a> ScopeType<'a> {
    /// Returns a ScopeType corresponding to the line fed
    fn new(line: &'a str) -> Self {
        lazy_static! {
            static ref NON_IMPL_FOR_DECLARATION: Regex = Regex::new(
                r"(?m)(?P<type>fn|trait|enum|struct|impl)(?:<.*?>)?\s+?(?P<name>\w+(?:<.*>)?)"
            )
            .unwrap();
            static ref IMPL_FOR_DECLARATION: Regex = Regex::new(
                r"(?m)impl(?:<.*>)\s+?(?P<trait>\w+(?:<.*?>)?)\s+?for\s+?(?P<type>\w+(?:<.*>)?)"
            )
            .unwrap();
        }
        if let Some(capture) = IMPL_FOR_DECLARATION.captures(line) {
            return ScopeType::Whereable(Whereable::Implementation(
                Some(capture.name("trait").unwrap().as_str()),
                capture.name("type").unwrap().as_str(),
            ));
        } else if let Some(capture) = NON_IMPL_FOR_DECLARATION.captures(line) {
            let name = capture.name("name").unwrap().as_str();
            let whereable: Whereable<'a> = match capture.name("type").unwrap().as_str() {
                "fn" => Whereable::Function(name),
                "struct" => Whereable::Structure(name),
                "enum" => Whereable::Enumeration(name),
                "impl" => Whereable::Implementation(None, name),
                "trait" => Whereable::Trait(name),
                other => {
                    panic!("capture matched `{}`, but no match arm existed for it", other);
                }
            };
            return ScopeType::Whereable(whereable);
        }
        ScopeType::Unnamed
    }
}

struct Scope<'a> {
    /// The offset of the scope-start (`{`)
    start: usize,
    scope_start: usize,
    scope_type: ScopeType<'a>,
}

fn find_parent_whereables(text: &str, position: lsp_types::Position) -> Vec<Scope<'_>> {
    let mut parents: Vec<Scope<'_>> = vec![];

    let mut line = 0;
    let mut offset_in_line = 0;
    let mut last_start = 0;
    for (count, character) in text.chars().enumerate() {
        if line == position.line && offset_in_line == position.character {
            return parents;
        }
        if character == '\n' {
            line += 1;
            offset_in_line = 0;
        } else {
            offset_in_line += 1;
            if character == '{' {
                parents.push(Scope {
                    start: last_start,
                    scope_start: count,
                    scope_type: ScopeType::new(&text[last_start..count]),
                });
                last_start = count;
            }
            if character == '}' {
                last_start = count;
                parents.pop();
            }
        }
    }
    parents.drain_filter(|scope| scope.scope_type == ScopeType::Unnamed);
    parents
}

fn generate_trait_bound_action(
    text: &str,
    scope: &Scope<'_>,
    clause_left: &str,
    clause_right: &str,
) -> Option<Suggestion> {
    let where_regex_left: String = r"(?m)where(?:.*?([, ]|\n)+".to_string();
    let where_regex_right = r"\s*:(?P<args>[^,{]*))?";
    let label =
        format!("Add where {}: {} clause to {}", clause_left, clause_right, scope.scope_type);
    let where_regex =
        Regex::new(&(where_regex_left + &regex::escape(clause_left) + where_regex_right)).unwrap();
    let (range, new_text) = if let Some(capture) =
        where_regex.captures(&text[scope.start..scope.scope_start])
    {
        if let Some(current_right_clause) = capture.name("args") {
            let position = offset_to_position(text, scope.start + current_right_clause.start())?;
            (lsp_types::Range::new(position, position), format!(" {} + ", clause_right))
        } else {
            let position = offset_to_position(text, scope.start + capture.get(0).unwrap().end())?;
            (
                lsp_types::Range::new(position, position),
                format!(" {}: {}, ", clause_left, clause_right),
            )
        }
    } else {
        let position = offset_to_position(text, scope.scope_start)?;
        (
            lsp_types::Range::new(position, position),
            format!(" where {}: {} ", clause_left, clause_right),
        )
    };
    Some(Suggestion { range, new_text, label })
}

fn append_trait_bound_actions(
    file_path: &Path,
    ctx: &InitActionContext,
    diagnostic: &Diagnostic,
    suggestions: &mut Vec<Suggestion>,
    clause_left: &str,
    clause_right: &str,
) {
    let text = match ctx.vfs.load_file(file_path) {
        Ok(FileContents::Text(text)) => text,
        _ => {
            return;
        }
    };
    for scope in find_parent_whereables(&text, diagnostic.range.start).iter() {
        if let Some(suggestion) =
            generate_trait_bound_action(&text, scope, clause_left, clause_right)
        {
            suggestions.push(suggestion);
        }
    }
}

pub fn parse_diagnostic_for_suggestions(
    file_path: &Path,
    ctx: &InitActionContext,
    diagnostic: &Diagnostic,
) -> Vec<Suggestion> {
    lazy_static! {
        static ref TRAIT_BOUND_HELP_REGEX: Regex =
            Regex::new(r"consider adding a `where (?P<left>.*?[^:]):(?P<right>[^:].*)` bound")
                .unwrap();
    }

    let mut results = vec![];
    if let Some(capture) = TRAIT_BOUND_HELP_REGEX.captures(&diagnostic.message) {
        let left = capture.name("left").unwrap().as_str();
        let right = capture.name("right").unwrap().as_str();
        append_trait_bound_actions(file_path, ctx, diagnostic, &mut results, left, right);
    }
    results
}
