use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use std::vec::Vec;
use syn::{Error, Expr, Ident, Token, braced, parse::Parse, parse_macro_input};

mod types {
    syn::custom_keyword!(u1);
    syn::custom_keyword!(i1);
    syn::custom_keyword!(u2);
    syn::custom_keyword!(i2);
    syn::custom_keyword!(u3);
    syn::custom_keyword!(i3);
    syn::custom_keyword!(u4);
    syn::custom_keyword!(i4);
    syn::custom_keyword!(u5);
    syn::custom_keyword!(i5);
    syn::custom_keyword!(u6);
    syn::custom_keyword!(i6);
    syn::custom_keyword!(u7);
    syn::custom_keyword!(i7);
    syn::custom_keyword!(u8);
    syn::custom_keyword!(i8);
    syn::custom_keyword!(u9);
    syn::custom_keyword!(i9);
    syn::custom_keyword!(u10);
    syn::custom_keyword!(i10);
    syn::custom_keyword!(u11);
    syn::custom_keyword!(i11);
    syn::custom_keyword!(u12);
    syn::custom_keyword!(i12);
    syn::custom_keyword!(u13);
    syn::custom_keyword!(i13);
    syn::custom_keyword!(u14);
    syn::custom_keyword!(i14);
    syn::custom_keyword!(u15);
    syn::custom_keyword!(i15);
    syn::custom_keyword!(u16);
    syn::custom_keyword!(i16);
    syn::custom_keyword!(u17);
    syn::custom_keyword!(i17);
    syn::custom_keyword!(u18);
    syn::custom_keyword!(i18);
    syn::custom_keyword!(u19);
    syn::custom_keyword!(i19);
    syn::custom_keyword!(u20);
    syn::custom_keyword!(i20);
    syn::custom_keyword!(u21);
    syn::custom_keyword!(i21);
    syn::custom_keyword!(u22);
    syn::custom_keyword!(i22);
    syn::custom_keyword!(u23);
    syn::custom_keyword!(i23);
    syn::custom_keyword!(u24);
    syn::custom_keyword!(i24);
    syn::custom_keyword!(u25);
    syn::custom_keyword!(i25);
    syn::custom_keyword!(u26);
    syn::custom_keyword!(i26);
    syn::custom_keyword!(u27);
    syn::custom_keyword!(i27);
    syn::custom_keyword!(u28);
    syn::custom_keyword!(i28);
    syn::custom_keyword!(u29);
    syn::custom_keyword!(i29);
    syn::custom_keyword!(u30);
    syn::custom_keyword!(i30);
    syn::custom_keyword!(u31);
    syn::custom_keyword!(i31);
    syn::custom_keyword!(u32);
    syn::custom_keyword!(i32);
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Sign {
    Signed,
    Unsigned,
}

// #[derive(Debug, Clone)]
struct Field {
    pub name: Ident,
    pub size: usize,
    pub offset: usize,
    pub sign: Sign,
    pub def: Option<Expr>,
}

// #[derive(Debug, Clone, PartialEq, Eq)]
struct Instr {
    name: Ident,
    fields: Vec<Field>,
}

// #[derive(Debug, Clone, PartialEq, Eq)]
struct InstrSet {
    name: Ident,
    inner: Vec<Instr>,
}

fn parse_type(input: syn::parse::ParseStream) -> syn::Result<(usize, Sign)> {
    if let Ok(_) = input.parse::<types::u1>() {
        Ok((1, Sign::Unsigned))
    } else if let Ok(_) = input.parse::<types::i1>() {
        Ok((1, Sign::Signed))
    } else if let Ok(_) = input.parse::<types::u2>() {
        Ok((2, Sign::Unsigned))
    } else if let Ok(_) = input.parse::<types::i2>() {
        Ok((2, Sign::Signed))
    } else if let Ok(_) = input.parse::<types::u3>() {
        Ok((3, Sign::Unsigned))
    } else if let Ok(_) = input.parse::<types::i3>() {
        Ok((3, Sign::Signed))
    } else if let Ok(_) = input.parse::<types::u4>() {
        Ok((4, Sign::Unsigned))
    } else if let Ok(_) = input.parse::<types::i4>() {
        Ok((4, Sign::Signed))
    } else if let Ok(_) = input.parse::<types::u5>() {
        Ok((5, Sign::Unsigned))
    } else if let Ok(_) = input.parse::<types::i5>() {
        Ok((5, Sign::Signed))
    } else if let Ok(_) = input.parse::<types::u6>() {
        Ok((6, Sign::Unsigned))
    } else if let Ok(_) = input.parse::<types::i6>() {
        Ok((6, Sign::Signed))
    } else if let Ok(_) = input.parse::<types::u7>() {
        Ok((7, Sign::Unsigned))
    } else if let Ok(_) = input.parse::<types::i7>() {
        Ok((7, Sign::Signed))
    } else if let Ok(_) = input.parse::<types::u8>() {
        Ok((8, Sign::Unsigned))
    } else if let Ok(_) = input.parse::<types::i8>() {
        Ok((8, Sign::Signed))
    } else if let Ok(_) = input.parse::<types::u9>() {
        Ok((9, Sign::Unsigned))
    } else if let Ok(_) = input.parse::<types::i9>() {
        Ok((9, Sign::Signed))
    } else if let Ok(_) = input.parse::<types::u10>() {
        Ok((10, Sign::Unsigned))
    } else if let Ok(_) = input.parse::<types::i10>() {
        Ok((10, Sign::Signed))
    } else if let Ok(_) = input.parse::<types::u11>() {
        Ok((11, Sign::Unsigned))
    } else if let Ok(_) = input.parse::<types::i11>() {
        Ok((11, Sign::Signed))
    } else if let Ok(_) = input.parse::<types::u12>() {
        Ok((12, Sign::Unsigned))
    } else if let Ok(_) = input.parse::<types::i12>() {
        Ok((12, Sign::Signed))
    } else if let Ok(_) = input.parse::<types::u13>() {
        Ok((13, Sign::Unsigned))
    } else if let Ok(_) = input.parse::<types::i13>() {
        Ok((13, Sign::Signed))
    } else if let Ok(_) = input.parse::<types::u14>() {
        Ok((14, Sign::Unsigned))
    } else if let Ok(_) = input.parse::<types::i14>() {
        Ok((14, Sign::Signed))
    } else if let Ok(_) = input.parse::<types::u15>() {
        Ok((15, Sign::Unsigned))
    } else if let Ok(_) = input.parse::<types::i15>() {
        Ok((15, Sign::Signed))
    } else if let Ok(_) = input.parse::<types::u16>() {
        Ok((16, Sign::Unsigned))
    } else if let Ok(_) = input.parse::<types::i16>() {
        Ok((16, Sign::Signed))
    } else if let Ok(_) = input.parse::<types::u17>() {
        Ok((17, Sign::Unsigned))
    } else if let Ok(_) = input.parse::<types::i17>() {
        Ok((17, Sign::Signed))
    } else if let Ok(_) = input.parse::<types::u18>() {
        Ok((18, Sign::Unsigned))
    } else if let Ok(_) = input.parse::<types::i18>() {
        Ok((18, Sign::Signed))
    } else if let Ok(_) = input.parse::<types::u19>() {
        Ok((19, Sign::Unsigned))
    } else if let Ok(_) = input.parse::<types::i19>() {
        Ok((19, Sign::Signed))
    } else if let Ok(_) = input.parse::<types::u20>() {
        Ok((20, Sign::Unsigned))
    } else if let Ok(_) = input.parse::<types::i20>() {
        Ok((20, Sign::Signed))
    } else if let Ok(_) = input.parse::<types::u21>() {
        Ok((21, Sign::Unsigned))
    } else if let Ok(_) = input.parse::<types::i21>() {
        Ok((21, Sign::Signed))
    } else if let Ok(_) = input.parse::<types::u22>() {
        Ok((22, Sign::Unsigned))
    } else if let Ok(_) = input.parse::<types::i22>() {
        Ok((22, Sign::Signed))
    } else if let Ok(_) = input.parse::<types::u23>() {
        Ok((23, Sign::Unsigned))
    } else if let Ok(_) = input.parse::<types::i23>() {
        Ok((23, Sign::Signed))
    } else if let Ok(_) = input.parse::<types::u24>() {
        Ok((24, Sign::Unsigned))
    } else if let Ok(_) = input.parse::<types::i24>() {
        Ok((24, Sign::Signed))
    } else if let Ok(_) = input.parse::<types::u25>() {
        Ok((25, Sign::Unsigned))
    } else if let Ok(_) = input.parse::<types::i25>() {
        Ok((25, Sign::Signed))
    } else if let Ok(_) = input.parse::<types::u26>() {
        Ok((26, Sign::Unsigned))
    } else if let Ok(_) = input.parse::<types::i26>() {
        Ok((26, Sign::Signed))
    } else if let Ok(_) = input.parse::<types::u27>() {
        Ok((27, Sign::Unsigned))
    } else if let Ok(_) = input.parse::<types::i27>() {
        Ok((27, Sign::Signed))
    } else if let Ok(_) = input.parse::<types::u28>() {
        Ok((28, Sign::Unsigned))
    } else if let Ok(_) = input.parse::<types::i28>() {
        Ok((28, Sign::Signed))
    } else if let Ok(_) = input.parse::<types::u29>() {
        Ok((29, Sign::Unsigned))
    } else if let Ok(_) = input.parse::<types::i29>() {
        Ok((29, Sign::Signed))
    } else if let Ok(_) = input.parse::<types::u30>() {
        Ok((30, Sign::Unsigned))
    } else if let Ok(_) = input.parse::<types::i30>() {
        Ok((30, Sign::Signed))
    } else if let Ok(_) = input.parse::<types::u31>() {
        Ok((31, Sign::Unsigned))
    } else if let Ok(_) = input.parse::<types::i31>() {
        Ok((31, Sign::Signed))
    } else if let Ok(_) = input.parse::<types::u32>() {
        Ok((32, Sign::Unsigned))
    } else if let Ok(_) = input.parse::<types::i32>() {
        Ok((32, Sign::Signed))
    } else {
        Err(Error::new(input.span(), "unknown type"))
    }
}

impl Parse for Field {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let name: Ident = input.parse()?;
        let _: Token![:] = input.parse()?;
        let (size, sign) = parse_type(input)?;
        let def = if let Ok(_) = input.parse::<Token![=]>() {
            Some(input.parse()?)
        } else {
            None
        };
        Ok(Field {
            name,
            size,
            offset: 0,
            sign: sign,
            def,
        })
    }
}

impl Parse for Instr {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let name: Ident = input.parse()?;
        let content;
        braced!(content in input);
        let mut fields: Vec<Field> = content
            .parse_terminated(Field::parse, Token![,])?
            .into_iter()
            .collect();

        let mut offset: usize = 0;
        for f in fields.iter_mut() {
            f.offset = offset;
            offset += f.size;
        }

        match offset.cmp(&{ u32::BITS as usize }) {
            std::cmp::Ordering::Less => Err(Error::new(name.span(), "Struct is too small")),
            std::cmp::Ordering::Equal => Ok(Instr { name, fields }),
            std::cmp::Ordering::Greater => Err(Error::new(name.span(), "Struct is too large")),
        }
    }
}

impl Parse for InstrSet {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let name: Ident = input.parse()?;
        let content;
        braced!(content in input);

        let mut elements = Vec::new();
        while !content.is_empty() {
            let el = content.parse()?;
            elements.push(el);
        }

        Ok(InstrSet {
            name,
            inner: elements,
        })
    }
}

impl Field {
    fn generate_type(&self) -> TokenStream {
        match self.sign {
            Sign::Signed => quote![i32],
            Sign::Unsigned => quote![u32],
        }
    }

    fn generate_bounds(&self) -> (TokenStream, TokenStream) {
        match self.sign {
            Sign::Signed => {
                let shr = i32::BITS as usize - self.size;
                let min = i32::min_value() >> shr;
                let max = i32::max_value() >> shr;
                (quote![#min], quote![#max])
            }
            Sign::Unsigned => {
                let shr = u32::BITS as usize - self.size;
                let min = u32::min_value() >> shr;
                let max = u32::max_value() >> shr;
                (quote![#min], quote![#max])
            }
        }
    }

    fn generate_getter(&self) -> TokenStream {
        let Field {
            name,
            size,
            offset,
            sign: _,
            def,
        } = self;

        let t = self.generate_type();

        let getter = format_ident!("get_{}", name);

        if let Some(value) = def {
            quote! {
                pub fn #getter(&self) -> #t {
                    #value as _
                }
            }
        } else {
            let getter_shl = u32::BITS as usize - size - offset;
            let getter_shr = u32::BITS as usize - size;

            quote! {
                pub fn #getter(&self) -> #t {
                    let Self {inner} = self;
                    let value = *inner as #t;
                    value << #getter_shl >> #getter_shr
                }
            }
        }
    }

    fn generate_setter(&self) -> TokenStream {
        let Field {
            name,
            size,
            offset,
            sign: _,
            def,
        } = self;

        let t = self.generate_type();

        let setter = format_ident!("set_{}", name);
        let mask: u32 =
            u32::max_value() << (u32::BITS as usize - size) >> (u32::BITS as usize - size - offset);

        let publicity = if def.is_some() {
            quote! {}
        } else {
            quote! {pub}
        };

        let (min, max) = self.generate_bounds();

        quote! {
            #publicity fn #setter(&mut self, value: #t) -> &mut Self {
                assert!(#min <= value && value <= #max);
                let Self {inner} = self;
                *inner &= !#mask;
                *inner |= ((value as u32) << #offset) & #mask;
                self
            }
        }
    }

    fn generate_ctr_field(&self) -> TokenStream {
        if self.def.is_some() {
            return quote! {};
        }

        let name = &self.name;
        let t = self.generate_type();
        quote! {
            #name: #t,
        }
    }

    fn generate_ctr_body(&self) -> TokenStream {
        let name = &self.name;
        let setter = format_ident!("set_{}", name);
        if let Some(v) = &self.def {
            quote! {
                result.#setter(#v as _);
            }
        } else {
            quote! {
                result.#setter(#name);
            }
        }
    }
}

impl Instr {
    fn generate(&self) -> TokenStream {
        let Instr { name, fields } = self;

        let getters: TokenStream = fields.iter().map(Field::generate_getter).collect();

        let setters: TokenStream = fields.iter().map(Field::generate_setter).collect();

        let ctr_fields: TokenStream = fields.iter().map(Field::generate_ctr_field).collect();
        let ctr_body: TokenStream = fields.iter().map(Field::generate_ctr_body).collect();

        quote! {
           #[derive(Debug, Copy, Clone, PartialEq, Eq)]
           pub struct #name {
               inner: u32
           }

           impl #name {
               pub fn from_raw(inner: u32) -> Self {
                   Self { inner }
               }

               pub fn from_fields(#ctr_fields) -> Self {
                   let mut result = Self::from_raw(0);
                   #ctr_body
                   result
               }

               pub fn raw(&self) -> u32 {
                   self.inner
               }

               #getters

               #setters
           }
        }
    }
}

impl InstrSet {
    fn generate(&self) -> TokenStream {
        let InstrSet { name, inner } = self;

        let instrs: TokenStream = inner.iter().flat_map(Instr::generate).collect();

        let enum_body: TokenStream = inner
            .into_iter()
            .flat_map(|x| {
                let inner_name = &x.name;
                quote! {
                    #inner_name(#inner_name),
                }
            })
            .collect();
        quote! {
           #[derive(Debug, Copy, Clone, PartialEq, Eq)]
            pub enum #name {
                #enum_body
            }

            #instrs
        }
    }
}

#[proc_macro]
pub fn gen_instr(tokens: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let instrs = parse_macro_input!(tokens as Instr);
    instrs.generate().into()
}

#[proc_macro]
pub fn gen_instr_set(tokens: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let instrs = parse_macro_input!(tokens as InstrSet);
    instrs.generate().into()
}
