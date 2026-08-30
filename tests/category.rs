//! The panic taxonomy and its bitset.

use panicgraph::{
    Category, CategorySet,
    category::{ALL, parse_selector},
};

#[test]
fn every_category_has_a_unique_bit() {
    let mut seen = 0u32;
    for category in ALL {
        assert_eq!(
            seen & category.bit(),
            0,
            "{category} reuses a bit already taken"
        );
        seen |= category.bit();
    }
}

#[test]
fn every_category_round_trips_through_its_name() {
    for category in ALL {
        let parsed: Category = category
            .name()
            .parse()
            .expect("a category name should parse back");
        assert_eq!(parsed, category);
    }
}

#[test]
fn set_operations_behave() {
    let mut set = CategorySet::EMPTY;
    assert!(set.is_empty());
    set.insert(Category::Index);
    set.insert(Category::Unwrap);
    assert_eq!(set.len(), 2);
    assert!(set.contains(Category::Index));

    let removed = set.difference(CategorySet::single(Category::Index));
    assert!(!removed.contains(Category::Index));
    assert!(removed.contains(Category::Unwrap));

    let both = removed.union(CategorySet::single(Category::Index));
    assert_eq!(both, set);
    assert_eq!(
        set.intersection(CategorySet::single(Category::Unwrap))
            .len(),
        1
    );
}

#[test]
fn oom_covers_allocation_but_not_reference_counts() {
    let oom = CategorySet::oom();
    assert!(oom.contains(Category::CapacityOverflow));
    assert!(oom.contains(Category::AllocFailure));
    assert!(
        !oom.contains(Category::RefCountOverflow),
        "a reference count overflow is an invariant failure, not allocator \
         exhaustion, so it must stay visible"
    );
}

#[test]
fn default_suppression_adds_precondition_checks() {
    let set = CategorySet::default_suppressed();
    assert!(set.contains_all(CategorySet::oom()));
    assert!(set.contains(Category::UbCheck));
    assert!(!set.contains(Category::Unwrap));
}

#[test]
fn selectors_accept_names_and_groups() {
    let set = parse_selector("unwrap, index").expect("both names are valid");
    assert!(set.contains(Category::Unwrap));
    assert!(set.contains(Category::Index));

    let oom = parse_selector("oom").expect("oom is a group alias");
    assert_eq!(oom, CategorySet::oom());

    let all = parse_selector("all").expect("all is a group alias");
    assert_eq!(all.len() as usize, ALL.len());

    assert_eq!(
        parse_selector("").expect("an empty selector is valid"),
        CategorySet::EMPTY
    );
}

#[test]
fn unknown_selector_names_the_offending_token() {
    assert_eq!(parse_selector("unwrap,bogus"), Err("bogus".to_owned()));
}
