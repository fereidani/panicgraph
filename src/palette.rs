//! The colours both renderings draw with, read from one file.
//!
//! The interactive view and the standalone drawing colour the same graph,
//! and a category has to be the same colour in both or a reader moving from
//! one to the other is misled. So the colours live in one file,
//! `assets/palette.json`, which the view fetches and the drawing embeds.
//!
//! Three hue families carry identity, because an icicle places arbitrary
//! frames side by side and only three categorical slots clear the all-pairs
//! colour vision floors. Within a family, each category has a step of its
//! own on the family's hue, so a picture of many categories reads as more
//! than three flat colours while the family still says what kind of panic
//! a frame is at a glance. A frame that is a call rather than a panic takes
//! a faint tint of the family most of the panics under it belong to. The
//! exact category is written on the frame and in its title, never left to
//! colour alone.

use anyhow::{Context, Result, bail, ensure};
use clap::ValueEnum;
use serde::Deserialize;

use crate::{Category, category::ALL, util::Map};

/// The palette file, embedded so the drawing and the view read the colours
/// of the build they came from.
pub const SOURCE: &str = include_str!("../assets/palette.json");

/// The darker of the two inks a label can take.
const DARK_INK: &str = "#0b0b0b";
/// The lighter of the two inks a label can take.
const LIGHT_INK: &str = "#ffffff";

/// The colours a picture is drawn in.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, ValueEnum)]
pub enum Theme {
    /// Dark marks on a light page.
    #[default]
    Light,
    /// Light marks on a dark page.
    Dark,
}

impl Theme {
    /// The name the file and the view know the theme by.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Light => "light",
            Self::Dark => "dark",
        }
    }
}

/// A hue family, which is what colour alone says about a panic.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Family {
    /// Logic and bounds: indexing, arithmetic, unwraps, explicit panics.
    Logic,
    /// Allocation.
    Alloc,
    /// Unverified: what the analysis could not read or classify.
    Unsure,
}

impl Family {
    /// Every family, in the order siblings of equal width are banded.
    pub const ALL: [Self; 3] = [Self::Logic, Self::Alloc, Self::Unsure];

    /// The name the file and the view know the family by.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Logic => "logic",
            Self::Alloc => "alloc",
            Self::Unsure => "unsure",
        }
    }
}

/// The file as a whole: which categories belong to which family, and the
/// colours of each theme.
#[derive(Debug, Deserialize)]
struct File {
    families: Families,
    light: Colours,
    dark: Colours,
}

/// The categories of each family, by name.
#[derive(Debug, Deserialize)]
struct Families {
    logic: Vec<String>,
    alloc: Vec<String>,
    unsure: Vec<String>,
}

impl Families {
    /// The family of every category, checking each is named exactly once.
    fn resolve(&self) -> Result<[Family; ALL.len()]> {
        let mut found = [None; ALL.len()];
        let listed = [
            (Family::Logic, &self.logic),
            (Family::Alloc, &self.alloc),
            (Family::Unsure, &self.unsure),
        ];
        for (family, names) in listed {
            for name in names {
                let Ok(category) = name.parse::<Category>() else {
                    bail!("the palette names an unknown category `{name}`");
                };
                let slot = &mut found[category as usize];
                ensure!(
                    slot.is_none(),
                    "the palette puts `{name}` in two families"
                );
                *slot = Some(family);
            }
        }
        let mut families = [Family::Unsure; ALL.len()];
        for (slot, category) in families.iter_mut().zip(ALL) {
            *slot = found[category as usize].with_context(|| {
                format!("the palette puts `{}` in no family", category.name())
            })?;
        }
        Ok(families)
    }
}

/// The colours of one theme, as written in the file.
#[derive(Debug, Clone, Deserialize)]
pub struct Colours {
    /// The page.
    pub page: String,
    /// The title, the controls, and the hovered frame's details.
    pub ink: String,
    /// Labels on frames that are calls rather than panics.
    pub label: String,
    /// The policy line and the notes.
    pub muted: String,
    /// The outline of a frame that runs only while unwinding.
    pub gate: String,
    /// What a search matched.
    #[serde(rename = "match")]
    pub matched: String,
    /// The mark in the corner.
    pub brand: String,
    /// The colour that stands for each family, for keys and legends.
    pub family: FamilyColours,
    /// Frames that are calls, tinted by the family beneath them.
    pub call: CallColours,
    /// Frames that are panics, by category name.
    pub panic: Map<String, String>,
}

/// One colour per family.
#[derive(Debug, Clone, Deserialize)]
pub struct FamilyColours {
    pub logic: String,
    pub alloc: String,
    pub unsure: String,
}

/// The tints a call takes, by the family beneath it.
#[derive(Debug, Clone, Deserialize)]
pub struct CallColours {
    /// A call with no family beneath it.
    pub none: String,
    pub logic: String,
    pub alloc: String,
    pub unsure: String,
}

impl Colours {
    /// Checks that every colour is written as `#rrggbb`.
    fn check(&self, theme: Theme) -> Result<()> {
        let fixed = [
            &self.page,
            &self.ink,
            &self.label,
            &self.muted,
            &self.gate,
            &self.matched,
            &self.brand,
            &self.family.logic,
            &self.family.alloc,
            &self.family.unsure,
            &self.call.none,
            &self.call.logic,
            &self.call.alloc,
            &self.call.unsure,
        ];
        for colour in fixed.into_iter().chain(self.panic.values()) {
            ensure!(
                is_colour(colour),
                "the palette's {} theme writes `{colour}`, which is not a \
                 colour of the form #rrggbb",
                theme.name()
            );
        }
        for category in ALL {
            ensure!(
                self.panic.contains_key(category.name()),
                "the palette's {} theme gives `{}` no colour",
                theme.name(),
                category.name()
            );
        }
        Ok(())
    }
}

/// The colours of one theme, with the family of every category.
#[derive(Debug, Clone)]
pub struct Palette {
    colours: Colours,
    /// The family of each category, indexed by discriminant.
    families: [Family; ALL.len()],
}

impl Palette {
    /// Reads the theme's colours out of the embedded file.
    ///
    /// # Errors
    ///
    /// Returns an error if the file does not parse, leaves a category
    /// without a family or a colour, names one twice, or writes a colour
    /// in any form but `#rrggbb`.
    pub fn load(theme: Theme) -> Result<Self> {
        let file: File = serde_json::from_str(SOURCE)
            .context("the palette file does not parse")?;
        let families = file.families.resolve()?;
        let colours = match theme {
            Theme::Light => file.light,
            Theme::Dark => file.dark,
        };
        colours.check(theme)?;
        Ok(Self { colours, families })
    }

    /// The colours of the theme, as written.
    #[must_use]
    pub const fn colours(&self) -> &Colours {
        &self.colours
    }

    /// The family a category belongs to.
    #[must_use]
    pub const fn family(&self, category: Category) -> Family {
        self.families[category as usize]
    }

    /// The colour of a panic of the category.
    #[must_use]
    pub fn panic(&self, category: Category) -> &str {
        // Loading checked that every category has a colour, so the fall
        // back cannot be reached; a call's own colour keeps it harmless.
        self.colours
            .panic
            .get(category.name())
            .map_or(&self.colours.call.none, String::as_str)
    }

    /// The tint of a call, by the family most of the panics under it
    /// belong to.
    #[must_use]
    pub fn call(&self, family: Option<Family>) -> &str {
        let call = &self.colours.call;
        match family {
            None => &call.none,
            Some(Family::Logic) => &call.logic,
            Some(Family::Alloc) => &call.alloc,
            Some(Family::Unsure) => &call.unsure,
        }
    }

    /// The colour that stands for a family.
    #[must_use]
    pub fn family_colour(&self, family: Family) -> &str {
        let set = &self.colours.family;
        match family {
            Family::Logic => &set.logic,
            Family::Alloc => &set.alloc,
            Family::Unsure => &set.unsure,
        }
    }
}

/// Whether text is a colour written as `#rrggbb`.
fn is_colour(text: &str) -> bool {
    text.strip_prefix('#').is_some_and(|hex| {
        hex.len() == 6 && hex.chars().all(|c| c.is_ascii_hexdigit())
    })
}

/// The ink that reads best on a fill.
///
/// Whichever of the two inks contrasts more, measured rather than guessed
/// from a lightness threshold, so a palette can be re-stepped without the
/// labels going unreadable. Anything that is not a colour takes the dark
/// ink, which reads on every page the themes have.
#[must_use]
pub fn ink_on(fill: &str) -> &'static str {
    let dark = contrast(fill, DARK_INK);
    let light = contrast(fill, LIGHT_INK);
    match (dark, light) {
        (Some(dark), Some(light)) if light > dark => LIGHT_INK,
        _ => DARK_INK,
    }
}

/// The contrast ratio between two colours, as the accessibility guidelines
/// define it, or nothing if either is not a colour.
#[must_use]
pub fn contrast(a: &str, b: &str) -> Option<f64> {
    let a = luminance(a)?;
    let b = luminance(b)?;
    Some((a.max(b) + 0.05) / (a.min(b) + 0.05))
}

/// Relative luminance of a colour written as `#rrggbb`.
fn luminance(hex: &str) -> Option<f64> {
    let hex = hex.strip_prefix('#')?;
    if hex.len() != 6 {
        return None;
    }
    let channel = |at: usize| -> Option<f64> {
        let byte = u8::from_str_radix(hex.get(at..at + 2)?, 16).ok()?;
        let c = f64::from(byte) / 255.0;
        Some(if c <= 0.04045 {
            c / 12.92
        } else {
            ((c + 0.055) / 1.055).powf(2.4)
        })
    };
    let red = 0.2126 * channel(0)?;
    let green = 0.7152f64.mul_add(channel(2)?, red);
    Some(0.0722f64.mul_add(channel(4)?, green))
}
