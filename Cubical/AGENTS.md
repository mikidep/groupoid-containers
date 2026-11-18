## Accountability

- Mark your output between comments
`-- BEGIN VIBE` and `-- END VIBE`
- When writing new definitions and proofs, prefix them with `-- TODO: check vibe`
- Your todos begin with `-- TODO: codex`, only address those

## Workspace usage

- Use temp directory in /tmp/codex-work when experimenting and testing instead of stopping and asking for permission for intermediate steps
- Keep updates to the main workspace atomic

## Writing proofs

- Use equational reasoning unless otherwise specified for proof obligations, i.e. equations between 2-cells
- Try using the reassoc! macro from Reflection.Reassoc whenever applicable, reverting to the manual reassoc from Prelude.Reassoc when this fails.
- When typechecking a module becomes too time or RAM intensive, split intensive parts out in helper modules, to better take advantage of Agda's caching.
- Explicit usages of reassoc go in separate files to keep the proofs clean

## Diagrams

- Equations between pastings should be represented rendering lhs and rhs as 2D pastings
- Arrows go left to right and top to bottom unless it's necessary to do otherwise
- Identities should be rendered with double lines, instead of arrows
- Use unicode when possible, e.g. α instead of alpha
- Respect my notations
    - F₀, F₁, F₂ for actions of functor F on 0-, 1- and 2-cells
    - no overloading especially on whiskerings, i.e. use ◃ and ▹ 
- Split 1- and 2- cells when applicable
- Replace objects with · when the diagrams become too crowded

## Reflection

- Make sure that macros fail instead of running forever, perhaps using a FUEL magic number
