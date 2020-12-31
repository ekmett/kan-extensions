kan-extensions
==============

[![Hackage](https://img.shields.io/hackage/v/kan-extensions.svg)](https://hackage.haskell.org/package/kan-extensions) [![Build Status](https://github.com/ekmett/kan-extensions/workflows/Haskell-CI/badge.svg)](https://github.com/ekmett/kan-extensions/actions?query=workflow%3AHaskell-CI)

This package provides tools for working with various Kan extensions and Kan lifts in Haskell.

Among the interesting bits included are:

* Right and left Kan extensions (`Ran` and `Lan`)
* Right and left Kan lifts (`Rift` and `Lift`)
* Multiple forms of the Yoneda lemma (`Yoneda`)
* The `Codensity` monad, which can be used to improve the asymptotic complexity of code over free monads (`Codensity`, `Density`)
* A "comonad to monad-transformer transformer" that is a special case of a right Kan lift. (`CoT`, `Co`)

Contact Information
-------------------

Contributions and bug reports are welcome!

Please feel free to contact me through github or on the #haskell IRC channel on irc.freenode.net.

-Edward Kmett
