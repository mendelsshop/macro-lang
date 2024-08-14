use crate::ast::{Ast, Pair, Symbol};

use std::iter::Peekable;

pub struct Reader(String);

impl Reader {
    pub fn new() -> Self {
        Self(String::new())
    }
    pub fn new_with_input(input: &impl ToString) -> Self {
        Self(input.to_string())
    }
}

#[derive(Debug)]
pub struct OwnedChars {
    pub(crate) string: String,
    pub(crate) position: usize,
}

impl Iterator for OwnedChars {
    type Item = char;

    fn next(&mut self) -> Option<char> {
        let c = self.string[self.position..].chars().next()?;
        self.position += c.len_utf8();
        Some(c)
    }
}

pub trait OwnedCharsExt {
    fn chars(self) -> OwnedChars;
}

impl OwnedCharsExt for String {
    fn chars(self) -> OwnedChars {
        OwnedChars {
            string: self,
            position: 0,
        }
    }
}

pub type Input = Peekable<OwnedChars>;

pub type ReaderInnerResult = Result<(Ast, Input), (String, Input)>;

impl Reader {
    // we have empty continuations for if we run out of input, but we can recover if we get more
    // input
    pub fn read(&mut self) -> Result<Ast, String> {
        let input = <String as Clone>::clone(&self.0).chars().peekable();
        match Self::read_inner(input, &mut || None) {
            Ok((ast, rest)) => {
                self.0 = rest.collect();
                Ok(ast)
            }
            Err((reason, rest)) => {
                self.0 = rest.collect();
                Err(reason)
            }
        }
    }
    pub fn read_with_continue(
        &mut self,
        mut empty_continuation: impl FnMut() -> String,
    ) -> Result<Ast, String> {
        let input = <String as Clone>::clone(&self.0).chars().peekable();
        match Self::read_inner(input, &mut || Some(empty_continuation())) {
            Ok((ast, rest)) => {
                self.0 = rest.collect();
                Ok(ast)
            }
            Err((reason, rest)) => {
                self.0 = rest.collect();
                Err(reason)
            }
        }
    }
    // #[trace(format_enter = "", format_exit = "")]
    pub(crate) fn read_inner(
        input: Input,
        empty_continuation: &mut impl FnMut() -> Option<String>,
    ) -> ReaderInnerResult {
        let mut input = Self::read_whitespace_and_comments(input).1;
        match input.peek() {
            // TODO: quote
            Some('(') => {
                input.next();
                Self::read_list(input, empty_continuation)
            }
            Some(')') => {
                input.next();
                Err(("unfinished pair".to_string(), input))
            }
            Some('\'') => {
                input.next();
                Self::read_inner(input, empty_continuation).map(|(quoted, input)| {
                    (
                        Ast::Pair(Box::new(Pair(
                            Ast::Symbol("quote".into()),
                            Ast::Pair(Box::new(Pair(quoted, Ast::TheEmptyList))),
                        ))),
                        input,
                    )
                })
            }
            Some(n) if n.is_ascii_digit() => Self::read_number(input),
            Some(_) => Self::read_symbol(input),
            None => empty_continuation()
                .ok_or((String::from("empty input"), input))
                .and_then(|input| {
                    let input = input.chars().peekable();
                    Self::read_inner(input, empty_continuation)
                }),
        }
    }

    // #[trace(format_enter = "", format_exit = "")]
    pub(crate) fn read_whitespace_and_comments(mut input: Input) -> (bool, Input) {
        let mut found = false;
        while let Some(c) = input.peek() {
            match c {
                ';' => {
                    found = true;
                    // we do find to skip untill we find newline, this is essentially
                    // what skip while does, but skip while returns a new type and we
                    // cannot do impl trait in type alias so this does not work for with
                    // my input type
                    input.find(|c| *c != '\n');
                }
                c if c.is_whitespace() => {
                    found = true;
                    input.next();
                }
                _ => break,
            }
        }
        (found, input)
    }

    // #[trace(format_enter = "", format_exit = "")]
    // parse symbol if not followed by space paren or comment
    // invariant Some('.') | Some(c) if c.is_ascci_digit() = input.peek()
    pub(crate) fn read_number(input: Input) -> ReaderInnerResult {
        let (first, mut input) = Self::read_digit(input);
        let (second, input) = {
            if input.peek().copied().filter(|c| *c == '.').is_some() {
                input.next();
                let (digits, input) = Self::read_digit(input);
                (format!(".{digits}"), input)
            } else {
                (String::new(), input)
            }
        };
        let (last, input) = Self::read_symbol_inner(input);
        match (first.as_str(), second.as_str(), last.as_str()) {
            ("", "." | "", "") => Err(("invalid syntax dangling dot".to_owned(), input)),
            (_, _, "") => match format!("{first}{second}").parse::<f64>() {
                Ok(n) => Ok((Ast::Number(n), input)),
                Err(e) => Err((e.to_string(), input)),
            },

            (first, second, _) => {
                let (last, input) = Self::read_symbol_inner(input);
                Ok((
                    Ast::Symbol(Symbol(format!("{first}{second}{last}").into(), 0)),
                    input,
                ))
            }
        }
    }
    pub(crate) fn read_digit(mut input: Input) -> (String, Input) {
        let mut number = String::new();
        while let Some(n) = input.peek().copied().filter(char::is_ascii_digit) {
            input.next();
            number.push(n);
        }
        (number, input)
    }
    // constraints input.next() == Some(c) if c != whitespace or comment or paren
    // #[trace(format_enter = "", format_exit = "")]
    pub(crate) fn read_symbol(input: Input) -> ReaderInnerResult {
        let (symbol, input) = Self::read_symbol_inner(input);
        Ok((Ast::Symbol(Symbol(symbol.into(), 0)), input))
    }

    // #[trace(format_enter = "", format_exit = "")]
    pub(crate) fn read_list(
        mut input: Input,
        empty_continuation: &mut impl FnMut() -> Option<String>,
    ) -> ReaderInnerResult {
        input = Self::read_whitespace_and_comments(input).1;
        match input.peek() {
            // TODO: dot tailed list and pair instead of list
            Some(')') => {
                input.next();
                Ok((Ast::TheEmptyList, input))
            }
            Some('.') => {
                let item: Ast;
                input.next();
                (item, input) = Self::read_inner(input, empty_continuation)?;
                input = Self::read_end_parenthesis(input, empty_continuation)?;
                Ok((item, input))
            }
            Some(_) => {
                let item: Ast;
                (item, input) = Self::read_inner(input, empty_continuation)?;
                let item2: Ast;
                (item2, input) = Self::read_list(input, empty_continuation)?;
                Ok((Ast::Pair(Box::new(Pair(item, item2))), input))
            }
            None => {
                input = empty_continuation()
                    .ok_or(("unfinished list".to_string(), input))
                    .map(|input| input.chars().peekable())?;

                Self::read_list(input, empty_continuation)
            }
        }
    }

    pub(crate) fn read_end_parenthesis(
        mut input: Input,
        empty_continuation: &mut impl FnMut() -> Option<String>,
    ) -> Result<Input, (String, Input)> {
        input = Self::read_whitespace_and_comments(input).1;
        match input.next() {
            Some(')') => Ok(input),
            Some(char) => Err((
                format!("invalid termination character of dotted list {char}"),
                input,
            )),
            None => {
                input = empty_continuation()
                    .ok_or(("unfinished list".to_string(), input))
                    .map(|input| input.chars().peekable())?;
                Self::read_end_parenthesis(input, empty_continuation)
            }
        }
    }

    pub(crate) fn read_symbol_inner(mut input: Input) -> (String, Input) {
        let mut str = String::new();
        while let Some(char) = input.peek().copied() {
            if char.is_whitespace() || ['(', ')', ';', '"', '\''].contains(&char) {
                break;
            }
            input.next();
            str.push(char);
        }
        (str, input)
    }
}
