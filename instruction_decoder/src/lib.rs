use ahash::{AHashMap, AHashSet};
use derivative::Derivative;
use itertools::Itertools;
use log::{debug, error, warn};
use proc_macro2::{Delimiter, Group, Ident, Literal, Spacing, Span, TokenStream, TokenTree};
use quote::{ToTokens, TokenStreamExt, quote};
use std::{collections::BTreeSet, fmt::Display, iter::Peekable, ops::Range};

extern crate proc_macro;

#[proc_macro]
pub fn decode_instructions(item: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let _ = env_logger::builder().write_style(env_logger::WriteStyle::Always).try_init();
    State::default().parse_token_stream(item.into()).into()
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
enum PrefixCombinationEntry {
    Opcode,
    Immediates,
    Prefix(String),
}

impl PrefixCombinationEntry {
    fn prefix(&self) -> Option<&String> {
        match self {
            Self::Prefix(prefix) => Some(prefix),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, Default)]
struct InstructionEncoding {
    opcode: usize,
    mask: usize,
    prefixes: AHashSet<String>,
    parameters: Vec<(String, AddressingMethod)>,
}

impl InstructionEncoding {
    fn is_dynamic(&self) -> bool {
        self.parameters.iter().map(|(_, method)| method.is_dynamic()).reduce(|a, b| a || b).unwrap_or_default()
    }

    fn resolve_parameter(
        addressing_modes: &AHashMap<String, AddressingMode>,
        prefixes: &AHashSet<String>,
        opcode: usize,
        parameter: &mut AddressingMethod,
        range_override: Option<Range<usize>>,
    ) -> Result<(), ()> {
        match parameter {
            AddressingMethod::Decode { name, range } => {
                if range.start == 0
                    && range.end == 0
                    && let Some(new_range) = range_override.as_ref()
                {
                    *range = new_range.clone();
                }

                let value = (opcode >> range.start) & ((1 << range.len()) - 1);
                let Some(mut addressing_method) = addressing_modes.get(name).and_then(|mode| mode.addressing_method_for(prefixes, value)).cloned() else {
                    return Err(());
                };

                Self::resolve_parameter(
                    addressing_modes,
                    prefixes,
                    opcode,
                    &mut addressing_method,
                    if range.start == 0 && range.end == 0 { None } else { Some(range.clone()) },
                )?;

                *parameter = addressing_method;
            }
            AddressingMethod::ImmediateUnsigned(range) => {
                *parameter = AddressingMethod::ConstantUnsigned((opcode >> range.start) & ((1 << range.len()) - 1));
            }
            AddressingMethod::ImmediateSigned(range) => {
                let mask = (1 << range.len()) - 1;
                let value = opcode >> range.start;

                *parameter = AddressingMethod::ConstantSigned(if value & (1 << (range.len() - 1)) != 0 {
                    (value | !mask) as isize
                } else {
                    (value & mask) as isize
                });
            }
            AddressingMethod::Indirect { lhs, rhs } => {
                Self::resolve_parameter(addressing_modes, prefixes, opcode, lhs, range_override.clone())?;

                if let Some(rhs) = rhs.as_mut() {
                    Self::resolve_parameter(addressing_modes, prefixes, opcode, rhs, range_override.clone())?;
                }
            }
            AddressingMethod::List(list) => {
                for method in list {
                    if Self::resolve_parameter(addressing_modes, prefixes, opcode, method, range_override.clone()).is_err() {
                        continue;
                    }

                    *parameter = method.clone();
                    return Ok(());
                }

                return Err(());
            }
            _ => (),
        }

        Ok(())
    }

    /// resolves all addressing modes that need to be decoded from the opcode
    fn resolve_parameters(&mut self, addressing_modes: &AHashMap<String, AddressingMode>, prefixes: &AHashSet<String>, opcode: usize) -> Result<(), ()> {
        for (_, parameter) in &mut self.parameters {
            Self::resolve_parameter(addressing_modes, prefixes, opcode, parameter, None)?;
        }

        Ok(())
    }
}

#[derive(Clone, Debug)]
enum AddressingMode {
    Dynamic(AHashMap<BTreeSet<String>, AHashMap<usize, AddressingMethod>>),
    Static(AHashMap<BTreeSet<String>, AddressingMethod>),
    None,
}

impl AddressingMode {
    fn prefixes<'a>(&'a self) -> Box<dyn Iterator<Item = &'a String> + 'a> {
        match self {
            Self::Dynamic(map) => Box::new(map.keys().flatten()),
            Self::Static(map) => Box::new(map.keys().flatten()),
            Self::None => Box::new([].iter()),
        }
    }

    fn addressing_method_for(&self, prefixes: &AHashSet<String>, value: usize) -> Option<&AddressingMethod> {
        match self {
            Self::Dynamic(map) => {
                let mut prefix_matches = map
                    .iter()
                    .filter(|(key, _)| key.len() == prefixes.len() && key.iter().all(|prefix| prefixes.contains(prefix)))
                    .collect::<Vec<_>>();
                prefix_matches.sort_by_key(|(key, _)| key.len());

                prefix_matches.iter().rev().filter_map(|(_, map)| map.get(&value)).next()
            }
            Self::Static(map) => map
                .iter()
                .filter(|(key, _)| key.len() == prefixes.len() && key.iter().all(|prefix| prefixes.contains(prefix)))
                .max_by_key(|(key, _)| key.len())
                .map(|(_, value)| value),
            Self::None => None,
        }
    }
}

#[derive(Clone, Derivative)]
#[derivative(Debug, Hash, PartialEq, Eq)]
enum AddressingMethod {
    Arbitrary {
        string_representation: String,
        #[derivative(PartialEq = "ignore")]
        #[derivative(Hash = "ignore")]
        stream: TokenStream,
    },
    Direct {
        lhs: Box<AddressingMethod>,
        rhs: Option<Box<AddressingMethod>>,
    },
    Indirect {
        lhs: Box<AddressingMethod>,
        rhs: Option<Box<AddressingMethod>>,
    },
    Immediate8Bit,
    Immediate16Bit,
    Decode {
        name: String,
        range: Range<usize>,
    },
    ImmediateSigned(Range<usize>),
    ImmediateUnsigned(Range<usize>),
    ConstantSigned(isize),
    ConstantUnsigned(usize),
    List(Vec<AddressingMethod>),
}

impl AddressingMethod {
    fn is_dynamic(&self) -> bool {
        match self {
            Self::Decode { .. } => true,
            Self::Direct { lhs, rhs } | Self::Indirect { lhs, rhs } => [lhs].into_iter().chain(rhs.iter()).any(|method| method.is_dynamic()),
            Self::List(list) => list.iter().any(AddressingMethod::is_dynamic),
            _ => false,
        }
    }

    fn immediate_size(&self) -> Option<usize> {
        match self {
            Self::Direct { lhs, rhs } | Self::Indirect { lhs, rhs } => {
                let result = lhs.immediate_size().unwrap_or_default() + rhs.as_ref().and_then(|rhs| rhs.immediate_size()).unwrap_or_default();

                if result == 0 { None } else { Some(result) }
            }
            Self::Immediate8Bit => Some(1),
            Self::Immediate16Bit => Some(2),
            _ => None,
        }
    }

    fn build_tokens(&self, immediates_index: &mut usize) -> TokenStream {
        match self {
            Self::Arbitrary { stream, .. } => stream.clone(),
            Self::Direct { lhs, rhs } => {
                let lhs_tokens = lhs.build_tokens(immediates_index);
                let rhs_tokens = rhs.as_ref().map(|rhs| rhs.build_tokens(immediates_index)).unwrap_or_else(|| quote! { Immediate::UnknownUnsigned(0) });
                quote! { direct(cpu_state, #lhs_tokens, #rhs_tokens)? }
            }
            Self::Indirect { lhs, rhs } => {
                let lhs_tokens = lhs.build_tokens(immediates_index);
                let rhs_tokens = rhs.as_ref().map(|rhs| rhs.build_tokens(immediates_index)).unwrap_or_else(|| quote! { Immediate::UnknownUnsigned(0) });
                quote! { indirect(cpu_state, #lhs_tokens, #rhs_tokens)? }
            }
            Self::ConstantSigned(value) => quote! { Immediate::UnknownSigned(#value) },
            Self::ConstantUnsigned(value) => quote! { Immediate::UnknownUnsigned(#value) },
            Self::Immediate8Bit => {
                let result = quote! { Immediate::Byte(immediate_bytes[#immediates_index]) };
                *immediates_index += 1;
                result
            }
            Self::Immediate16Bit => {
                let result = quote! { Immediate::Word(u16::from_le_bytes(immediate_bytes[#immediates_index..#immediates_index + 2].try_into().unwrap())) };
                *immediates_index += 2;
                result
            }
            Self::Decode { .. } | Self::ImmediateSigned(_) | Self::ImmediateUnsigned(_) | Self::List(_) => unimplemented!(),
        }
    }
}

impl Display for AddressingMethod {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Arbitrary { string_representation: value, .. } => write!(f, "{value}"),
            Self::Direct { lhs, rhs } => {
                write!(f, "direct({lhs}")?;

                if let Some(rhs) = &rhs {
                    write!(f, " + {rhs}")?;
                }

                write!(f, ")")
            }
            Self::Indirect { lhs, rhs } => {
                write!(f, "indirect({lhs}")?;

                if let Some(rhs) = &rhs {
                    write!(f, " + {rhs}")?;
                }

                write!(f, ")")
            }
            Self::Immediate8Bit => write!(f, "imm8()"),
            Self::Immediate16Bit => write!(f, "imm16()"),
            Self::Decode { name, range } => {
                if range.start == 0 && range.end == 0 {
                    write!(f, "{name}()")
                } else {
                    write!(f, "{name}({}..{})", range.start, range.end)
                }
            }
            Self::ImmediateSigned(range) => write!(f, "imm_signed({}..{})", range.start, range.end),
            Self::ImmediateUnsigned(range) => write!(f, "imm_unsigned({}..{})", range.start, range.end),
            Self::ConstantSigned(value) => write!(f, "{value}"),
            Self::ConstantUnsigned(value) => write!(f, "{value}"),
            Self::List(list) => write!(f, "{}", list.iter().map(|method| method.to_string()).join(" | ")),
        }
    }
}

#[derive(Default, Debug)]
struct PrefixSet {
    prefix_name_set: AHashSet<String>,
    prefix_modifiers: AHashSet<String>,
    prefixes: AHashMap<usize, String>,
}

#[derive(Default, Debug, Clone)]
struct InstructionDefinition {
    name: Option<String>,
    encodings: Vec<InstructionEncoding>,
    body: Option<TokenStream>,
}

#[derive(Debug, Clone)]
struct SingleEncoding<'a> {
    name: Option<String>,
    encoding: InstructionEncoding,
    body: Option<&'a TokenStream>,
}

impl Display for SingleEncoding<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.name {
            Some(name) => write!(f, "{}", name)?,
            None => {
                write!(
                    f,
                    "\"{}\"",
                    format!("{:08b}", self.encoding.opcode)
                        .chars()
                        .zip(format!("{:08b}", self.encoding.mask).chars())
                        .map(|(opcode, mask)| if mask == '1' { '*' } else { opcode })
                        .collect::<String>(),
                )?;

                if !self.encoding.prefixes.is_empty() {
                    write!(f, " ({})", self.encoding.prefixes.iter().join(" + "))?;
                }
            }
        }

        if !self.encoding.parameters.is_empty() && !f.alternate() {
            write!(
                f,
                ", {}",
                self.encoding.parameters.iter().map(|(name, addressing_method)| format!("{name}: {addressing_method}")).join(", "),
            )?;
        }

        Ok(())
    }
}

#[derive(Default)]
struct State {
    instruction_word_size: usize,
    should_trace_instructions: bool,
    prefix_set: PrefixSet,
    prefix_lists: AHashSet<Vec<PrefixCombinationEntry>>,
    addressing_modes: AHashMap<String, AddressingMode>,
    instruction_definitions: Vec<InstructionDefinition>,
    invalid_instruction_handler: Option<TokenStream>,
    unimplemented_instruction_handler: Option<TokenStream>,
    instruction_return_type: Option<TokenStream>,
}

impl State {
    /// parses the top level token stream of this macro, divided up into individual sections
    fn parse_token_stream(&mut self, item: TokenStream) -> TokenStream {
        let mut token_iterator = item.into_iter().peekable();

        while token_iterator.peek().is_some() {
            let Some(TokenTree::Ident(identifier)) = token_iterator.next() else {
                panic!("expected identifier");
            };

            let Some(TokenTree::Punct(punct)) = token_iterator.next() else {
                panic!("expected \":\"");
            };
            assert!(punct.as_char() == ':' && punct.spacing() == Spacing::Alone, "expected \":\"");

            match token_iterator.next() {
                Some(TokenTree::Group(group)) => {
                    assert!(group.delimiter() == Delimiter::Brace, "expected brace-delimited group");

                    let token_stream = group.stream();
                    match identifier.to_string().as_str() {
                        "prefixes" => self.parse_prefixes_group(token_stream),
                        "prefix_combinations" => self.parse_prefix_combinations_group(token_stream),
                        "addressing_modes" => self.parse_addressing_modes_group(token_stream),
                        "instructions" => self.parse_instructions_group(token_stream),
                        "invalid_instruction_handler" => self.invalid_instruction_handler = Some(token_stream),
                        "unimplemented_instruction_handler" => self.unimplemented_instruction_handler = Some(token_stream),
                        "return_type" => self.instruction_return_type = Some(token_stream),
                        _ => panic!("unknown group name \"{identifier}\""),
                    };
                }
                Some(TokenTree::Literal(literal)) => {
                    match identifier.to_string().as_str() {
                        "instruction_word_size" => self.instruction_word_size = Self::parse_integer(literal),
                        _ => panic!("unknown constant name \"{identifier}\""),
                    };
                }
                Some(TokenTree::Ident(other_ident)) => {
                    match identifier.to_string().as_str() {
                        "trace_instructions" => self.should_trace_instructions = Self::parse_boolean(other_ident),
                        _ => panic!("unknown constant name \"{identifier}\""),
                    };
                }
                _ => panic!("expected brace-delimited group, literal, or identifier"),
            }

            if token_iterator.peek().is_some() {
                let Some(TokenTree::Punct(punct)) = token_iterator.next() else {
                    panic!("expected \",\"");
                };
                assert!(punct.as_char() == ',' && punct.spacing() == Spacing::Alone, "expected \",\"");
            }
        }

        assert!(self.instruction_word_size != 0, "instruction word size must be defined");
        assert!(self.invalid_instruction_handler.is_some(), "missing invalid instruction handler");

        if self.unimplemented_instruction_handler.is_none() {
            warn!("unimplemented instruction handler wasn't provided, using default implementation that will panic");

            self.unimplemented_instruction_handler = Some(quote! {
                panic!("unimplemented instruction {instruction_as_string}");
            });
        }

        self.check_prefix_definitions();
        self.build_tables()
    }

    fn parse_integer(literal: Literal) -> usize {
        let literal_string = literal.to_string();

        if literal_string.len() >= 2 {
            let radix = match &literal_string[..2] {
                "0x" => 16,
                "0o" => 8,
                "0b" => 2,
                _ => 10,
            };

            usize::from_str_radix(if radix == 10 { &literal_string } else { &literal_string[2..] }, radix).expect("expected integer literal")
        } else {
            literal_string.parse().expect("expected integer literal")
        }
    }

    fn parse_boolean(identifier: Ident) -> bool {
        match identifier.to_string().as_str() {
            "true" => true,
            "false" => false,
            _ => panic!("expected boolean"),
        }
    }

    fn parse_arrow(token_iterator: &mut Peekable<impl Iterator<Item = TokenTree>>) -> bool {
        let Some(TokenTree::Punct(punct)) = token_iterator.peek() else {
            return false;
        };

        if punct.as_char() != '=' || punct.spacing() != Spacing::Joint {
            return false;
        }

        token_iterator.next();

        let Some(TokenTree::Punct(punct)) = token_iterator.peek() else {
            return false;
        };

        if punct.as_char() != '>' || punct.spacing() != Spacing::Alone {
            return false;
        }

        token_iterator.next();

        true
    }

    /// parses the section which acts as a list of prefixes
    fn parse_prefixes_group(&mut self, item: TokenStream) {
        let mut token_iterator = item.into_iter().peekable();

        while token_iterator.peek().is_some() {
            let Some(TokenTree::Literal(literal)) = token_iterator.next() else {
                panic!("expected integer literal");
            };

            assert!(Self::parse_arrow(&mut token_iterator), "expected \"=>\"");

            let Some(TokenTree::Ident(identifier)) = token_iterator.next() else {
                panic!("expected identifier");
            };

            let prefix_name = identifier.to_string();

            if let Some(TokenTree::Group(group)) = token_iterator.peek().cloned()
                && group.delimiter() == Delimiter::Parenthesis
            {
                token_iterator.next();

                let mut group_token_iterator = group.stream().into_iter().peekable();
                let Some(TokenTree::Ident(identifier)) = group_token_iterator.next() else {
                    panic!("expected identifier");
                };

                assert!(group_token_iterator.next().is_none(), "expected \")\"");

                match identifier.to_string().as_str() {
                    "modifier" => {
                        self.prefix_set.prefix_modifiers.insert(prefix_name.clone());
                    }
                    other => panic!("unknown prefix type {other:?}"),
                }
            }

            if token_iterator.peek().is_some() {
                let Some(TokenTree::Punct(punct)) = token_iterator.next() else {
                    panic!("expected \",\"");
                };
                assert!(punct.as_char() == ',' && punct.spacing() == Spacing::Alone, "expected \",\"");
            }

            self.prefix_set.prefix_name_set.insert(prefix_name.clone());
            self.prefix_set.prefixes.insert(Self::parse_integer(literal), prefix_name);
        }
    }

    /// parses the section that lists which order prefixes can appear in
    fn parse_prefix_combinations_group(&mut self, item: TokenStream) {
        let mut token_iterator = item.into_iter().peekable();

        while token_iterator.peek().is_some() {
            let mut list = Vec::new();

            while token_iterator.peek().is_some() {
                let Some(TokenTree::Ident(identifier)) = token_iterator.next() else {
                    panic!("expected identifier");
                };

                list.push(match identifier.to_string().as_str() {
                    "opcode" => PrefixCombinationEntry::Opcode,
                    "immediates" => PrefixCombinationEntry::Immediates,
                    _ => PrefixCombinationEntry::Prefix(identifier.to_string()),
                });

                if token_iterator.peek().is_none() {
                    break;
                }

                let Some(TokenTree::Punct(punct)) = token_iterator.next() else {
                    panic!("expected \"+\" or \",\"");
                };
                assert!((punct.as_char() == '+' || punct.as_char() == ',') && punct.spacing() == Spacing::Alone, "expected \"+\" or \",\"");

                if punct.as_char() == ',' {
                    break;
                }
            }

            self.prefix_lists.insert(list);
        }
    }

    /// parses the section that lists addressing modes
    fn parse_addressing_modes_group(&mut self, item: TokenStream) {
        let mut token_iterator = item.into_iter().peekable();

        while token_iterator.peek().is_some() {
            let Some(TokenTree::Ident(identifier)) = token_iterator.next() else {
                panic!("expected identifier");
            };

            let Some(TokenTree::Punct(punct)) = token_iterator.next() else {
                panic!("expected \":\"");
            };
            assert!(punct.as_char() == ':' && punct.spacing() == Spacing::Alone, "expected \":\"");

            let Some(TokenTree::Group(group)) = token_iterator.next() else {
                panic!("expected brace-delimited group");
            };
            assert!(group.delimiter() == Delimiter::Brace, "expected brace-delimited group");

            if token_iterator.peek().is_some() {
                let Some(TokenTree::Punct(punct)) = token_iterator.next() else {
                    panic!("expected \",\"");
                };
                assert!(punct.as_char() == ',' && punct.spacing() == Spacing::Alone, "expected \",\"");
            }

            let mut addressing_mode = AddressingMode::None;
            Self::parse_addressing_mode(&mut addressing_mode, group.stream(), Vec::new());

            assert!(!matches!(addressing_mode, AddressingMode::None), "addressing modes cannot be empty");
            self.addressing_modes.insert(identifier.to_string(), addressing_mode);
        }
    }

    /// parses an addressing mode definition
    fn parse_addressing_mode(addressing_mode: &mut AddressingMode, item: TokenStream, prefixes: Vec<String>) {
        let mut token_iterator = item.into_iter().peekable();

        while token_iterator.peek().is_some() {
            match token_iterator.next() {
                Some(TokenTree::Ident(prefix_identifier)) => {
                    if let Some(method) = Self::parse_qualified_identifier(&mut token_iterator, prefix_identifier.clone()) {
                        // this is a register or something like that

                        if let AddressingMode::Static(methods) = addressing_mode {
                            methods.insert(BTreeSet::from_iter(prefixes.clone().into_iter()), method);
                        } else if matches!(addressing_mode, AddressingMode::None) {
                            *addressing_mode = AddressingMode::Static(AHashMap::from_iter([(BTreeSet::from_iter(prefixes.clone().into_iter()), method)]));
                        } else {
                            panic!("can't mix static and dynamic addressing methods");
                        }
                    } else if let Some(TokenTree::Group(arguments_group)) = token_iterator.peek().cloned()
                        && arguments_group.delimiter() == Delimiter::Parenthesis
                    {
                        // this is a special addressing mode

                        token_iterator.next();

                        let method = Self::partial_parse_addressing_method(&mut token_iterator, prefix_identifier, arguments_group);

                        if let AddressingMode::Static(methods) = addressing_mode {
                            methods.insert(BTreeSet::from_iter(prefixes.clone().into_iter()), method);
                        } else if matches!(addressing_mode, AddressingMode::None) {
                            *addressing_mode = AddressingMode::Static(AHashMap::from_iter([(BTreeSet::from_iter(prefixes.clone().into_iter()), method)]));
                        } else {
                            panic!("can't mix static and dynamic addressing methods");
                        }
                    } else {
                        // this is a block of prefixes

                        let mut new_prefixes = Vec::from_iter(prefixes.iter().cloned().chain([prefix_identifier.to_string()]));

                        while let Some(TokenTree::Punct(punct)) = token_iterator.peek().cloned()
                            && punct.spacing() == Spacing::Alone
                            && punct.as_char() == '+'
                        {
                            token_iterator.next();

                            let Some(TokenTree::Ident(identifier)) = token_iterator.next() else {
                                panic!("expected identifier");
                            };

                            new_prefixes.push(identifier.to_string());
                        }

                        if !Self::parse_arrow(&mut token_iterator) {
                            panic!("expected \"=>\"");
                        }

                        let Some(TokenTree::Group(group)) = token_iterator.next() else {
                            panic!("expected brace-delimited group");
                        };
                        assert!(group.delimiter() == Delimiter::Brace, "expected brace-delimited group");

                        Self::parse_addressing_mode(addressing_mode, group.stream(), new_prefixes);
                    }
                }
                Some(TokenTree::Literal(literal)) => {
                    let value = Self::parse_integer(literal);

                    assert!(Self::parse_arrow(&mut token_iterator), "expected \"=>\"");

                    let addressing_method = Self::parse_addressing_method(&mut token_iterator).expect("expected addressing method");

                    let prefix_set = BTreeSet::from_iter(prefixes.clone().into_iter());

                    if let AddressingMode::Dynamic(methods) = addressing_mode {
                        if let Some(map) = methods.get_mut(&prefix_set) {
                            map.insert(value, addressing_method);
                        } else {
                            methods.insert(prefix_set, AHashMap::from_iter([(value, addressing_method)]));
                        }
                    } else if matches!(addressing_mode, AddressingMode::None) {
                        *addressing_mode = AddressingMode::Dynamic(AHashMap::from_iter([(prefix_set, AHashMap::from_iter([(value, addressing_method)]))]));
                    } else {
                        panic!("can't mix static and dynamic addressing methods");
                    }
                }
                Some(_) => panic!("expected identifier or literal"),
                None => unreachable!(),
            }

            if token_iterator.peek().is_some() {
                let Some(TokenTree::Punct(punct)) = token_iterator.next() else {
                    panic!("expected \",\"");
                };
                assert!(punct.as_char() == ',' && punct.spacing() == Spacing::Alone, "expected \",\"");
            }
        }
    }

    fn parse_qualified_identifier(token_iterator: &mut Peekable<impl Iterator<Item = TokenTree>>, first_identifier: Ident) -> Option<AddressingMethod> {
        let mut string_representation = first_identifier.to_string();
        let mut stream = TokenStream::from(TokenTree::Ident(first_identifier));
        let mut has_any = false;

        while let Some(TokenTree::Punct(punct)) = token_iterator.peek().cloned()
            && punct.as_char() == ':'
            && punct.spacing() == Spacing::Joint
        {
            token_iterator.next();

            let Some(TokenTree::Punct(punct_2)) = token_iterator.next() else {
                panic!("expected \"::\"");
            };
            assert!(punct_2.as_char() == ':' && punct_2.spacing() == Spacing::Alone, "expected \"::\"");

            let Some(TokenTree::Ident(other_identifier)) = token_iterator.next() else {
                panic!("expected identifier");
            };

            string_representation.push_str("::");
            string_representation.push_str(&other_identifier.to_string());
            stream.append(TokenTree::Punct(punct));
            stream.append(TokenTree::Punct(punct_2));
            stream.append(TokenTree::Ident(other_identifier));

            has_any = true;
        }

        if has_any { Some(AddressingMethod::Arbitrary { string_representation, stream }) } else { None }
    }

    /// parses an addressing method (either a register, an immediate, an indirection, or a reference to an addressing mode if applicable)
    fn parse_addressing_method(token_iterator: &mut Peekable<impl Iterator<Item = TokenTree>>) -> Option<AddressingMethod> {
        let Some(TokenTree::Ident(identifier)) = token_iterator.peek().cloned() else {
            return None;
        };

        token_iterator.next();

        if let Some(result) = Self::parse_qualified_identifier(token_iterator, identifier.clone()) {
            return Some(result);
        }

        let Some(TokenTree::Group(arguments_group)) = token_iterator.next() else {
            panic!("expected parenthesis-delimited group");
        };
        assert!(arguments_group.delimiter() == Delimiter::Parenthesis, "expected parenthesis-delimited group");

        Some(Self::partial_parse_addressing_method(token_iterator, identifier, arguments_group))
    }

    /// parses a special addressing method from its components (an identifier and arguments group)
    fn partial_parse_addressing_method(token_iterator: &mut Peekable<impl Iterator<Item = TokenTree>>, identifier: Ident, arguments_group: Group) -> AddressingMethod {
        let first_method = match identifier.to_string().as_str() {
            "imm8" => AddressingMethod::Immediate8Bit,
            "imm16" => AddressingMethod::Immediate16Bit,
            "direct" => {
                let mut group_token_iterator = arguments_group.stream().into_iter().peekable();
                let lhs = Self::parse_addressing_method(&mut group_token_iterator).expect("expected addressing method");
                let rhs = group_token_iterator
                    .next()
                    .and_then(|token| {
                        if let TokenTree::Punct(punct) = token
                            && punct.spacing() == Spacing::Alone
                            && punct.as_char() == '+'
                        {
                            Self::parse_addressing_method(&mut group_token_iterator)
                        } else {
                            panic!("expected \"+\"");
                        }
                    })
                    .map(Box::new);

                AddressingMethod::Direct { lhs: Box::new(lhs), rhs }
            }
            "indirect" => {
                let mut group_token_iterator = arguments_group.stream().into_iter().peekable();
                let lhs = Self::parse_addressing_method(&mut group_token_iterator).expect("expected addressing method");
                let rhs = group_token_iterator
                    .next()
                    .and_then(|token| {
                        if let TokenTree::Punct(punct) = token
                            && punct.spacing() == Spacing::Alone
                            && punct.as_char() == '+'
                        {
                            Self::parse_addressing_method(&mut group_token_iterator)
                        } else {
                            panic!("expected \"+\"");
                        }
                    })
                    .map(Box::new);

                AddressingMethod::Indirect { lhs: Box::new(lhs), rhs }
            }
            "const" => {
                let mut group_token_iterator = arguments_group.stream().into_iter().peekable();

                let Some(TokenTree::Literal(literal)) = group_token_iterator.next() else {
                    panic!("expected integer literal");
                };

                assert!(group_token_iterator.next().is_none(), "expected \")\"");
                AddressingMethod::ConstantUnsigned(Self::parse_integer(literal))
            }
            method => {
                let mut range = 0..0;

                if !arguments_group.stream().is_empty() {
                    let mut group_token_iterator = arguments_group.stream().into_iter();

                    let Some(TokenTree::Literal(start)) = group_token_iterator.next() else {
                        panic!("expected integer literal");
                    };

                    let Some(TokenTree::Punct(punct)) = group_token_iterator.next() else {
                        panic!("expected \"..\"");
                    };
                    assert!(punct.as_char() == '.' && punct.spacing() == Spacing::Joint, "expected \"..\"");

                    let Some(TokenTree::Punct(punct)) = group_token_iterator.next() else {
                        panic!("expected \"..\"");
                    };
                    assert!(punct.as_char() == '.' && punct.spacing() == Spacing::Alone, "expected \"..\"");

                    let Some(TokenTree::Literal(end)) = group_token_iterator.next() else {
                        panic!("expected integer literal");
                    };

                    assert!(group_token_iterator.next().is_none(), "expected \")\"");

                    range = Self::parse_integer(start)..Self::parse_integer(end);
                }

                match method {
                    "imm_signed" => AddressingMethod::ImmediateSigned(range),
                    "imm_unsigned" => AddressingMethod::ImmediateUnsigned(range),
                    _ => AddressingMethod::Decode { name: method.to_string(), range },
                }
            }
        };

        let mut methods = vec![first_method];

        while let Some(TokenTree::Punct(punct)) = token_iterator.peek()
            && punct.as_char() == '|'
            && punct.spacing() == Spacing::Alone
        {
            token_iterator.next();
            methods.push(Self::parse_addressing_method(token_iterator).expect("expected addressing method"));
        }

        if methods.len() != 1 {
            AddressingMethod::List(methods)
        } else {
            // this should just be methods[0] but rust is silly
            methods.into_iter().next().unwrap()
        }
    }

    /// parses the section that lists specific instruction encodings
    fn parse_instructions_group(&mut self, item: TokenStream) {
        let mut token_iterator = item.into_iter().peekable();

        while token_iterator.peek().is_some() {
            let name = if let Some(TokenTree::Literal(literal)) = token_iterator.peek().cloned() {
                token_iterator.next();

                let Some(TokenTree::Punct(punct)) = token_iterator.next() else {
                    panic!("expected \":\"");
                };
                assert!(punct.as_char() == ':' && punct.spacing() == Spacing::Alone, "expected \":\"");

                let string = literal.to_string();
                assert!(string.starts_with('"') && string.ends_with('"'), "expected string literal");

                Some(string.chars().skip(1).take(string.chars().count() - 2).collect::<String>())
            } else {
                None
            };

            let Some(TokenTree::Group(encoding_group)) = token_iterator.next() else {
                panic!("expected bracket-delimited group");
            };
            assert!(encoding_group.delimiter() == Delimiter::Bracket, "expected bracket-delimited group");

            assert!(Self::parse_arrow(&mut token_iterator), "expected \"=>\"");

            let body = match token_iterator.next() {
                Some(TokenTree::Group(body_group)) if body_group.delimiter() == Delimiter::Brace => Some(body_group.stream()),
                Some(TokenTree::Ident(identifier)) if identifier == "unimplemented" => None,
                _ => panic!("expected brace-delimited group or \"unimplemented\""),
            };

            if token_iterator.peek().is_some() {
                let Some(TokenTree::Punct(punct)) = token_iterator.next() else {
                    panic!("expected \",\"");
                };
                assert!(punct.as_char() == ',' && punct.spacing() == Spacing::Alone, "expected \",\"");
            }

            let encodings = Self::parse_instruction_encoding(encoding_group.stream());

            self.instruction_definitions.push(InstructionDefinition { name, encodings, body });
        }
    }

    /// parses the individual instruction encoding definitions and returns them as a list
    fn parse_instruction_encoding(item: TokenStream) -> Vec<InstructionEncoding> {
        let mut token_iterator = item.into_iter().peekable();
        let mut result = Vec::new();

        while token_iterator.peek().is_some() {
            let mut encoding = InstructionEncoding::default();

            let Some(TokenTree::Literal(match_literal)) = token_iterator.next() else {
                panic!("expected string literal");
            };
            let match_string = match_literal.to_string();

            assert!(match_string.starts_with('"') && match_string.ends_with('"'), "expected string literal");

            let match_string = match_string.chars().skip(1).take(match_string.chars().count() - 2).filter(|c| *c != '_').collect::<String>();

            assert!(
                match_string.chars().all(|c| matches!(c, '0' | '1' | '*')),
                "match string {match_string:?} must only contain the characters 0, 1, *, and _"
            );

            encoding.opcode = usize::from_str_radix(&match_string.replace('*', "0"), 2).unwrap();
            encoding.mask = usize::from_str_radix(&match_string.replace(['0', '1'], "0").replace('*', "1"), 2).unwrap();

            if let Some(TokenTree::Group(prefixes_group)) = token_iterator.peek()
                && prefixes_group.delimiter() == Delimiter::Parenthesis
            {
                {
                    let mut token_iterator = prefixes_group.stream().into_iter().peekable();

                    while token_iterator.peek().is_some() {
                        let Some(TokenTree::Ident(identifier)) = token_iterator.next() else {
                            panic!("expected identifier");
                        };
                        let prefix_name = identifier.to_string();

                        encoding.prefixes.insert(prefix_name);

                        if token_iterator.peek().is_some() {
                            let Some(TokenTree::Punct(punct)) = token_iterator.next() else {
                                panic!("expected \"+\"");
                            };
                            assert!(punct.as_char() == '+' && punct.spacing() == Spacing::Alone, "expected \"+\"");
                        }
                    }
                }

                token_iterator.next();
            }

            while token_iterator.peek().is_some() {
                let Some(TokenTree::Punct(punct)) = token_iterator.next() else {
                    panic!("expected \",\"");
                };
                assert!(punct.as_char() == ',' && punct.spacing() == Spacing::Alone, "expected \",\"");

                if matches!(token_iterator.peek(), Some(TokenTree::Literal(_)) | None) {
                    break;
                }

                let Some(TokenTree::Ident(identifier)) = token_iterator.next() else {
                    panic!("expected identifier");
                };
                let variable_name = identifier.to_string();

                let Some(TokenTree::Punct(punct)) = token_iterator.next() else {
                    panic!("expected \":\"");
                };
                assert!(punct.as_char() == ':' && punct.spacing() == Spacing::Alone, "expected \":\"");

                let addressing_method = Self::parse_addressing_method(&mut token_iterator).expect("expected addressing method");

                encoding.parameters.push((variable_name, addressing_method));
            }

            result.push(encoding);
        }

        result
    }

    /// makes sure all referenced prefixes are defined in the prefixes section
    fn check_prefix_definitions(&self) {
        let prefix_list_entries = self.prefix_lists.iter().flatten().filter_map(PrefixCombinationEntry::prefix);

        let addressing_mode_entries = self.addressing_modes.values().flat_map(|addressing_mode| addressing_mode.prefixes());

        let instruction_definition_entries = self.instruction_definitions.iter().flat_map(|definition| &definition.encodings).flat_map(|encoding| &encoding.prefixes);

        let mut iterator = prefix_list_entries.chain(addressing_mode_entries).chain(instruction_definition_entries);

        if let Some(prefix) = iterator.find(|entry| !self.prefix_set.prefix_name_set.contains(*entry)) {
            panic!("prefix {prefix:?} isn't defined in the prefixes section");
        }
    }

    /// finds a matching instruction definition given a set of prefixes and an opcode
    fn find_matching_instruction(&self, prefixes: &AHashSet<String>, opcode: usize) -> Option<SingleEncoding<'_>> {
        let mut iter = self.instruction_definitions.iter().flat_map(|definition| {
            definition
                .encodings
                .iter()
                .filter(|encoding| {
                    let opcode_matches = (opcode & !encoding.mask) == encoding.opcode;
                    let prefixes_match = if encoding.is_dynamic() {
                        encoding.prefixes.iter().all(|prefix| prefixes.contains(prefix))
                    } else {
                        *prefixes == encoding.prefixes
                    };

                    opcode_matches && prefixes_match
                })
                .filter_map(|encoding| {
                    let mut encoding = encoding.clone();
                    let mut new_prefixes = prefixes.clone();

                    // TODO: optimize this, this isn't a good way to do this
                    for prefix in &encoding.prefixes {
                        new_prefixes.remove(prefix);
                    }

                    let result = encoding.resolve_parameters(&self.addressing_modes, &new_prefixes, opcode);

                    result
                        .map(|_| SingleEncoding {
                            name: definition.name.clone(),
                            encoding,
                            body: definition.body.as_ref(),
                        })
                        .ok()
                })
                .collect::<Vec<_>>()
        });

        let result = iter.next();
        let others = iter.collect::<Vec<_>>();

        if !others.is_empty() {
            warn!(
                "instruction conflict with opcode {opcode:#010b} and prefixes {prefixes:?}! selected {}, other options: {}",
                result.as_ref().unwrap(),
                others.iter().map(|item| item.to_string()).join(", ")
            );
        }

        result
    }

    fn are_immediates_before_opcode(list: &[PrefixCombinationEntry]) -> bool {
        match list[list.len() - 2..] {
            [PrefixCombinationEntry::Opcode, PrefixCombinationEntry::Immediates] => false,
            [PrefixCombinationEntry::Immediates, PrefixCombinationEntry::Opcode] => true,
            _ => panic!("prefix combination entry must end in either \"opcode + immediates\" or \"immediates + opcode\""),
        }
    }

    /// gets the size of immediates required to parse instructions with a given prefix.
    /// invalid instructions are ignored and don't affect the result
    fn constant_immediates_size(&self, prefixes: &AHashSet<String>) -> usize {
        let mut iter = (0..(1 << (self.instruction_word_size * 8)))
            .flat_map(|opcode| self.find_matching_instruction(prefixes, opcode))
            .map(|instruction| instruction.encoding.parameters.iter().flat_map(|(_, method)| method.immediate_size()).sum::<usize>());

        let value = iter.clone().max().unwrap_or_default();

        if !iter.all(|i| i == value) {
            warn!("immediate size isn't constant with prefixes {prefixes:?}, using maximum value of {value} bytes");
        }

        value
    }

    /// creates the actual tables of functions used for instruction decoding
    // TODO: generalize memory access here
    fn build_tables(&self) -> TokenStream {
        let mut prefix_lists = self.prefix_lists.iter().collect::<Vec<_>>();
        prefix_lists.sort();
        prefix_lists.sort_by_key(|list| list.len());

        let instruction_word_size = proc_macro2::Literal::usize_unsuffixed(self.instruction_word_size);
        let int_type = proc_macro2::Ident::new(&format!("u{}", self.instruction_word_size * 8), Span::call_site());
        let mut output = quote! {};

        for (list_index, prefix_list) in prefix_lists.iter().enumerate().rev() {
            let immediates_before_opcode = Self::are_immediates_before_opcode(prefix_list);
            let prefixes = prefix_list.iter().filter_map(PrefixCombinationEntry::prefix).cloned().collect();

            debug!("list_{list_index}: {prefix_list:?}");

            let mut token_stream = quote! {};

            for i in 0..(1 << (self.instruction_word_size * 8)) {
                let found_instruction = self.find_matching_instruction(&prefixes, i);

                if let Some(prefix_name) = self.prefix_set.prefixes.get(&i)
                    && let Some((other_list_index, other_list)) = prefix_lists.iter().enumerate().skip(list_index + 1).find(|(_, other_list)| {
                        other_list
                            .iter()
                            .filter_map(PrefixCombinationEntry::prefix)
                            .zip(prefix_list.iter().filter_map(PrefixCombinationEntry::prefix).chain([prefix_name]))
                            .all(|(a, b)| a == b)
                    })
                {
                    if let Some(instruction) = found_instruction {
                        error!("prefix {prefix_name:?} ({i:#x}) conflicts with instruction {instruction}, choosing prefix");
                    }

                    assert!(!immediates_before_opcode, "additional prefixes can't be added with immediate before opcode encoding");
                    let next_immediates_before_opcode = Self::are_immediates_before_opcode(other_list);

                    debug!(
                        "    {i:#x}: adding {prefix_name:?} (list_{other_list_index}{})",
                        if next_immediates_before_opcode { ", immediates before opcode" } else { "" },
                    );

                    let list_name = proc_macro2::Ident::new(&format!("list_{other_list_index}"), Span::call_site());

                    let tokens = if next_immediates_before_opcode {
                        let constant_immediates_size = self.constant_immediates_size(&other_list.iter().filter_map(PrefixCombinationEntry::prefix).cloned().collect());
                        let bytes_to_read = Literal::usize_unsuffixed(constant_immediates_size + self.instruction_word_size);

                        quote! {
                            std::boxed::Box::new({
                                let #list_name = #list_name.clone();
                                move |cpu_state| {
                                    let mut bytes = [0; #bytes_to_read];

                                    cpu_state.mmu.read_memory(cpu_state.system_status_registers.master_status.user_system_bit(), crate::mmu::AccessType::Program, cpu_state.register_file.pc, &mut bytes)?;
                                    cpu_state.register_file.pc += #bytes_to_read;

                                    return #list_name[#int_type::from_le_bytes(bytes[#constant_immediates_size..].try_into().unwrap()) as usize](cpu_state, &bytes[..#constant_immediates_size]);
                                }
                            }),
                        }
                    } else {
                        quote! {
                            std::boxed::Box::new({
                                let #list_name = #list_name.clone();
                                move |cpu_state| {
                                    let mut opcode_bytes = [0; #instruction_word_size];

                                    cpu_state.mmu.read_memory(cpu_state.system_status_registers.master_status.user_system_bit(), crate::mmu::AccessType::Program, cpu_state.register_file.pc, &mut opcode_bytes)?;
                                    cpu_state.register_file.pc += #instruction_word_size;

                                    return #list_name[#int_type::from_le_bytes(opcode_bytes) as usize](cpu_state);
                                }
                            }),
                        }
                    };

                    tokens.to_tokens(&mut token_stream);
                } else if let Some(instruction) = found_instruction {
                    debug!("    {i:#x}: {instruction}");

                    let body = match instruction.body {
                        Some(body) => body,
                        None => self.unimplemented_instruction_handler.as_ref().unwrap(),
                    };
                    let mut parameters = quote! {};
                    let mut immediates_index = 0;
                    let instruction_as_string = instruction.to_string();
                    let trace_call = if self.should_trace_instructions {
                        let mut formatting_string = format!("{instruction:#}");

                        for (name, _) in &instruction.encoding.parameters {
                            formatting_string.push_str(&format!(", {name}: {{{name}:?}}"));
                        }

                        quote! {
                            {
                                use log::trace;
                                trace!(#formatting_string);
                            }
                        }
                    } else {
                        quote! {}
                    };

                    for (name, addressing_method) in &instruction.encoding.parameters {
                        let name_identifier = proc_macro2::Ident::new(name, Span::call_site());

                        let addressing_method_tokens = addressing_method.build_tokens(&mut immediates_index);
                        let tokens = quote! {
                            let #name_identifier = #addressing_method_tokens;
                        };

                        tokens.to_tokens(&mut parameters);
                    }

                    let tokens = if immediates_before_opcode {
                        quote! {
                            std::boxed::Box::new(|cpu_state, immediate_bytes| {
                                let instruction_as_string = #instruction_as_string;
                                #parameters
                                #trace_call
                                #body
                            }),
                        }
                    } else {
                        let immediates_length = instruction.encoding.parameters.iter().filter_map(|(_, method)| method.immediate_size()).sum::<usize>();
                        let immediate_bytes = if immediates_length == 0 {
                            quote! {}
                        } else {
                            let immediates_length = Literal::usize_unsuffixed(immediates_length);

                            quote! {
                                let mut immediate_bytes = [0; #immediates_length];

                                cpu_state.mmu.read_memory(cpu_state.system_status_registers.master_status.user_system_bit(), crate::mmu::AccessType::Program, cpu_state.register_file.pc, &mut immediate_bytes)?;
                                cpu_state.register_file.pc += #immediates_length;
                            }
                        };

                        quote! {
                            std::boxed::Box::new(|cpu_state| {
                                let instruction_as_string = #instruction_as_string;
                                #immediate_bytes
                                #parameters
                                #trace_call
                                #body
                            }),
                        }
                    };

                    tokens.to_tokens(&mut token_stream);

                    //debug!("{tokens}");
                } else {
                    let body = self.invalid_instruction_handler.clone().unwrap();
                    let mut prefix_tokens = quote! {};
                    let mut prefix_list_length = 0_usize;

                    for prefix in *prefix_list {
                        if let PrefixCombinationEntry::Prefix(prefix) = prefix {
                            quote! { #prefix, }.to_tokens(&mut prefix_tokens);
                            prefix_list_length += 1;
                        }
                    }

                    let tokens = if immediates_before_opcode {
                        quote! {
                            std::boxed::Box::new(|cpu_state, _| {
                                let opcode = #i;
                                let prefixes: [&str; #prefix_list_length] = [#prefix_tokens];
                                #body
                            }),
                        }
                    } else {
                        quote! {
                            std::boxed::Box::new(|cpu_state| {
                                let opcode = #i;
                                let prefixes: [&str; #prefix_list_length] = [#prefix_tokens];
                                #body
                            }),
                        }
                    };

                    tokens.to_tokens(&mut token_stream);
                }
            }

            let list_name = proc_macro2::Ident::new(&format!("list_{list_index}"), Span::call_site());
            let list_type = match immediates_before_opcode {
                true => quote! { InstructionListWithImmediates<T> },
                false => quote! { InstructionList<T> },
            };
            let tokens = quote! {
                let #list_name: #list_type = std::rc::Rc::new([#token_stream]);
            };

            tokens.to_tokens(&mut output);
        }

        if prefix_lists.first().unwrap().iter().any(|entry| matches!(entry, PrefixCombinationEntry::Prefix(_))) {
            panic!("prefix combinations list is missing a root entry");
        }

        let list_length = 1_usize << (self.instruction_word_size * 8);
        let root_list_name = proc_macro2::Ident::new("list_0", Span::call_site());
        let return_type = self.instruction_return_type.clone().unwrap_or_else(|| quote! { () });

        // TODO: handle immediates before opcode for the root instruction table

        quote! {
            type InstructionList<T> = std::rc::Rc<[Box<dyn Fn(&mut crate::CPUState<T>) -> #return_type>; #list_length]>;
            type InstructionListWithImmediates<T> = std::rc::Rc<[std::boxed::Box<dyn Fn(&mut crate::CPUState<T>, &[u8]) -> #return_type>; #list_length]>;

            pub struct InstructionDecoder<T>
            where T: crate::BusAccessor + 'static
            {
                root_list: InstructionList<T>,
            }

            impl<T> InstructionDecoder<T>
            where T: crate::BusAccessor + 'static
            {
                pub fn decode_instruction(&self, cpu_state: &mut crate::CPUState<T>) -> #return_type {
                    let mut opcode_bytes = [0; #instruction_word_size];

                    cpu_state.mmu.read_memory(cpu_state.system_status_registers.master_status.user_system_bit(), crate::mmu::AccessType::Program, cpu_state.register_file.pc, &mut opcode_bytes)?;
                    cpu_state.register_file.pc += #instruction_word_size;

                    return self.root_list[#int_type::from_le_bytes(opcode_bytes) as usize](cpu_state);
                }
            }

            impl<T> Default for InstructionDecoder<T>
            where T: crate::BusAccessor + 'static
            {
                fn default() -> Self {
                    #output
                    Self { root_list: #root_list_name }
                }
            }
        }
    }
}
