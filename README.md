# Fabric

## Setup

### Dependencies

First, install the WebAssembly toolchain – [`binaryen`](https://github.com/WebAssembly/binaryen/). For instance, using Homebrew:

```bash
brew install binaryen
```

Unfortunately, Homebrew does not ship a `pkg-config` file that Dune relies on. One workaround is to create a file `/opt/homebrew/lib/pkgconfig/libbinaryen.pc` with the following contents:

```
prefix=/opt/homebrew/Cellar/binaryen/121/
libdir=${prefix}/lib
includedir=${prefix}/include

Name: libbinaryen
Description: Manual entry for homebrew installation of binaryen.
Version: 121
Libs: -L${libdir} -lbinaryen
Cflags: -I${includedir}
```

### Build

The project is built using Dune.

Clone the repository and create a local switch for the project: 

```bash
git clone https://github.com/jbachurski/fabric.git
cd fabric
opam switch create .
```

Now, you should be able to `dune build` and `dune runtest`. To run the compiler, use `dune exec fabric`, which prints a help message.

## Examples

See the [tests](test/test_fabric.ml) for now.
