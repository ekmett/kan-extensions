5.2.2 [2021.02.17]
------------------
* Add `hoistCoyoneda` to `Data.Functor.Contravariant.Coyoneda`.

5.2.1 [2020.10.01]
------------------
* Allow building with GHC 9.0.

5.2 [2018.07.03]
----------------
* Make `Codensity` levity polymorphic.
* Add the `Data.Functor.Invariant.Day` module, which combines the covariant and
  contravariant versions of `Day`. As a result, `kan-extensions` now depends on
  the `invariant` package.
* Add a `wrapCodensity` function.
* More efficient `Eq1`, `Ord1`, and `Adjunction` instances for `Coyoneda`.
* Add `INLINE` pragmas on more functions.
* Allow building with `containers-0.6`.

5.1 [2018.01.28]
----------------
* Make `Density`, `Codensity`, `Kan` and `Lan` polykinded.
* Add `Eq1`, `Ord1`, `Read1` and `Show1` instances for `Coyoneda` and `Yoneda`.
* Change contexts of `Eq` and `Ord` instances of `Coyoneda` and `Yoneda`
  (and the `Show` instance for `Coyoneda`) to require lifted class instances,
  e.g. `Eq1 f, Eq a`.
* Allow `free-5`.

5.0.2
-----
* Added `hoistCoyoneda`

5.0.1
-----
* Removed some redundant constraints

5
-----
* Move `Data.Functor.Kan.Rift` to `Data.Functor.Day.Curried`

4.2.3
-----
* Builds clean on GHC 7.10

4.2.2
-----
* `semigroupoids` 5 support

4.2.1
---
* Add `liftRift` and `lowerRift`

4.2
---
* Remove pointed dependency

4.1.1
---
* Added `Applicative` instance for `Day`
* Added `Typeable` instance for `Codensity`

4.1.0.1
----
* Added `tagged` dependency

4.1
---
* Moved co- and contra- variant `Day` convolution from `contravariant` to here. Day convolution is intimately connected to `Rift`.

4.0.3
-----
* Added `liftCoT0M`, `liftCoT1M`, `diter` and `dctrlM` for using `CoT w m` to model a state machine with states in `w` and effects in `m`.

4.0.2
-----
* Made fixes necessary to work around changes in `ImpredicativeTypes` for GHC 7.8.1rc2

4.0.1
-----
* Bug fix so we can compile on GHC 7.4

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

