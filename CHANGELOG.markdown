4.0
---
* Removed `keys` dependency
* Now compatible with `adjunctions` 4.0

3.7
---
* Moved all the `Yoneda` variants around again.
* Improved haddocks

3.6.2
-----
* Added `Data.Functor.Contravariant.Yoneda` to complete the set of Yoneda embeddings/reductions.

3.6.1
-----
* Added several missing isomorphisms

3.6
---
* `instance Monad m => MonadSpec (Yoneda m)`

3.5.1
-----
* Fixed a bug in the signature for `composedRepToCodensity`.

3.5
---
* More combinators for `Rift`/`Lift`.
* Added combinators for working with representable functors rather than just adjoint functors.
* Split `Data.Functor.KanExtension` into `Data.Functor.Kan.Ran` and `Data.Functor.Kan.Lan`
* Split `Data.Functor.KanLift` into `Data.Functor.Kan.Rift` and `Data.Functor.Kan.Lift`
* Moved from `Data.Functor.Yoneda.Contravariant` to `Data.Functor.Yoneda.Reduction` adopting terminology from Todd Trimble.
* Added various missing isomorphisms.
* Greatly improved the Haddocks for this package stating laws and derivations where we can (especially for 'Rift' and 'Ran').

3.3
---
* Rift is now `Applicative`. Added `rap`.

3.2
---
* Added right and left Kan lifts under `Data.Functor.KanLift`.
* Decreased reliance on the `Composition` class where unnecessary in the API

3.1.2
-----
* Marked modules `Trustworthy` as required for `SafeHaskell` in the presence of these extensions.

3.1.1
-----
* Refactored build system
* IRC build-bot notification
* Removed upper bounds on dependencies on my other packages

3.1
---
* Moved `Control.Monad.Free.Church` over to the `free` package instead and removed it from `kan-extensions`

