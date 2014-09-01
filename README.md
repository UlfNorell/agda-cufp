
## Programming with Dependent Types

### Getting Started

#### Prerequisites
- Haskell Platform
- Emacs
- git

#### Installing Agda
- cabal update
- cabal install Agda
- agda-mode setup

#### Getting the libraries
- git clone https://github.com/UlfNorell/agda-prelude
- git clone https://github.com/UlfNorell/agda-cufp
- cd agda-prelude/agda-ffi
- cabal install

#### Set up Emacs paths
- M-x agda2-mode
- M-x customize-group agda2
- Add the **absolute** path to agda-prelude/src to Include Dirs (on a new line under ".")

#### Check that it works
- Open agda-cufp/exercises/Lambda.agda in Emacs
- Hit `C-c C-l` to type check
- Hit `C-c C-x C-c` to compile
- You should now have an executable Lambda in exercises/
- Run `./Lambda example.lam`. This should print a desugared lambda term and the
  result of running it through the SECD machine.

### Resources

- [Agda Wiki](http://wiki.portal.chalmers.se/agda/pmwiki.php)
- [Mailing list](https://lists.chalmers.se/mailman/listinfo/agda)
- [IRC channel #agda on freenode](http://webchat.freenode.net)
- `doc/AgdaCheatSheet.agda` contains a number of small examples showing some of the features of Agda.
- `doc/EmacsCheatSheet.html` lists the most commonly used Emacs mode commands.
- Browse the library. Use `M-.` or `middle mouse` to jump to the definitions of library functions.

### Exercises

- TBA
