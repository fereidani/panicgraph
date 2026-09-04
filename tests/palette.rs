//! The colours the interactive view and the standalone drawing share.

#![cfg(any(feature = "serve", feature = "svg"))]

use panicgraph::{
    Category,
    category::ALL,
    palette::{Family, Palette, Theme, contrast, ink_on},
};

/// Every theme the file has.
const THEMES: [Theme; 2] = [Theme::Light, Theme::Dark];

/// Loads one theme, failing the test if the file is not what is expected.
fn load(theme: Theme) -> Palette {
    Palette::load(theme).expect("the palette file should load")
}

#[test]
fn both_themes_colour_every_category() {
    for theme in THEMES {
        let palette = load(theme);
        for category in ALL {
            let fill = palette.panic(category);
            assert!(
                fill.starts_with('#') && fill.len() == 7,
                "{} in {theme:?} is drawn in `{fill}`",
                category.name()
            );
        }
    }
}

#[test]
fn every_category_belongs_to_a_family_and_every_family_has_members() {
    let palette = load(Theme::Light);
    for family in Family::ALL {
        assert!(
            ALL.iter()
                .any(|category| palette.family(*category) == family),
            "{family:?} has no category"
        );
    }
    assert_eq!(palette.family(Category::Unwrap), Family::Logic);
    assert_eq!(palette.family(Category::AllocFailure), Family::Alloc);
    assert_eq!(palette.family(Category::DynCall), Family::Unsure);
}

#[test]
fn two_categories_of_one_family_are_told_apart() {
    for theme in THEMES {
        let palette = load(theme);
        assert_ne!(
            palette.panic(Category::Unwrap),
            palette.panic(Category::Index),
            "each category has a step of its own in {theme:?}"
        );
        assert_ne!(
            palette.panic(Category::Unknown),
            palette.panic(Category::DynCall),
            "each category has a step of its own in {theme:?}"
        );
    }
}

#[test]
fn a_label_reads_on_every_frame() {
    for theme in THEMES {
        let palette = load(theme);
        for category in ALL {
            let fill = palette.panic(category);
            let ink = ink_on(fill);
            let ratio = contrast(fill, ink).expect("both are colours");
            assert!(
                ratio >= 4.4,
                "{} on {fill} in {theme:?} reads at {ratio:.2}",
                category.name()
            );
        }
        let colours = palette.colours();
        let calls = &colours.call;
        for tint in [&calls.none, &calls.logic, &calls.alloc, &calls.unsure] {
            let ratio =
                contrast(tint, &colours.label).expect("both are colours");
            assert!(
                ratio >= 4.4,
                "the label ink on {tint} in {theme:?} reads at {ratio:.2}"
            );
        }
    }
}

#[test]
fn the_ink_falls_back_to_dark_on_what_is_not_a_colour() {
    assert_eq!(ink_on("nope"), "#0b0b0b");
    assert_eq!(ink_on("#fff"), "#0b0b0b");
    assert!(contrast("#fff", "#000000").is_none());
    assert_eq!(ink_on("#ffffff"), "#0b0b0b");
    assert_eq!(ink_on("#000000"), "#ffffff");
}
