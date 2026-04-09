# social-choice-theory

Lean 4 formalization of finite social choice theory, currently centered on:

- foundational definitions for preferences and profiles on finite agendas,
- Arrow's impossibility theorem,
- a strict-ballot Gibbard-Satterthwaite theorem derived from Arrow.

The project is being refactored toward the terminology and conventions used in
[eco-lean](https://github.com/RitinkarDB/eco-lean), so the public-facing API now
prefers names such as `Preference`, `Profile`, `ParetoOn`, `IIAOn`, and
`DictatorialOn`.

## Current Structure

The main development lives in three files:

- `SocialChoiceTheory/Basic.lean`
  - finite-set lemmas used in social-choice arguments,
  - weak preference as the primitive notion,
  - derived strict preference and indifference,
  - maximality / best-element / choice-set notions,
  - bundled order structures, including the eco-lean-facing alias `Preference`,
  - shared social-choice vocabulary such as `Profile`,
    `SocialChoiceFunction`, `SocialWelfareFunction`, `PairwiseAgreesOn`,
    `ParetoOn`, `IIAOn`, `IsDictatorOn`, and `DictatorialOn`.

- `SocialChoiceTheory/Arrow.lean`
  - a finite-agenda proof of Arrow's theorem via the classical pivot argument,
  - theorem statements phrased in the shared `Basic.lean` terminology,
  - legacy names retained as compatibility aliases where useful.

- `SocialChoiceTheory/GibbardSatterthwaite.lean`
  - a strict-ballot Gibbard-Satterthwaite development following Nipkow's
    pair-top construction,
  - forward-facing operations `prefers`, `weakPref`, and `toPreference` for
    interoperability with eco-lean,
  - a public theorem layer that mirrors the same style of axioms and
    dictatorship notions used on the Arrow side.

There is currently no top-level umbrella module or executable entrypoint in the
repository. The old `Main.lean` / `SocialChoiceTheory.lean` files were removed,
so the project is best treated as a small collection of directly-importable Lean
modules.

## Terminology Conventions

The refactor aims to make this repository read more like eco-lean:

- weak preference is primary,
- strict preference is derived from weak preference,
- theorem statements are phrased using `Preference` and `Profile`,
- social-choice axioms are stated with shared names such as `ParetoOn`,
  `IIAOn`, and `DictatorialOn`,
- older names are kept only as compatibility scaffolding while the transition
  is still in progress.

At the moment, this is largely true at the statement and API level. Some proof
internals, especially on the strict-ballot side, still retain older
presentation choices for compatibility with the original development.

## Dependencies

- Lean `v4.20.0-rc5`
- [mathlib](https://github.com/leanprover-community/mathlib4)
- [Canonical](https://github.com/chasenorman/Canonical)

These are declared in `lakefile.toml`.

## Checking The Files

Because the current `lakefile.toml` still mentions an executable rooted at
`Main`, direct file checking is the most reliable way to work with the
repository in its present state.

From the repository root:

```bash
lake env lean SocialChoiceTheory/Basic.lean
lake env lean SocialChoiceTheory/Arrow.lean
lake env lean SocialChoiceTheory/GibbardSatterthwaite.lean
```

If you want a cleaner package-level workflow later, the next step would be to
update `lakefile.toml` so that its targets match the current module structure.

## Background And References

The development is influenced in particular by:

- Wulf Gaertner, [A Primer in Social Choice Theory](https://academic.oup.com/book/52348)
- [Handbook of Computational Social Choice](https://cgi.cse.unsw.edu.au/~haziz/comsoc.pdf)

The long-term direction is to bring this material closer to the conventions and
infrastructure of [eco-lean](https://github.com/RitinkarDB/eco-lean).
