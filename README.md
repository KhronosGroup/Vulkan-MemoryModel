# Vulkan-MemoryModel

The Vulkan-MemoryModel repo includes documentation and tools related to the
Vulkan Memory Model that are not built into the core specification.

## License

This repo is treated as an offshoot of the Vulkan-Docs repo, and uses the
same Creative Commons Attribution 4.0 license. See [COPYING.md](COPYING.md).

[Alloy](http://alloy.lcs.mit.edu/alloy/index.html) is a third-party tool
used in this repo, and is available from
http://alloy.lcs.mit.edu/alloy/download.html.

## Alloy Model

The [alloy](alloy) subdirectory includes an Alloy [implementation](alloy/spirv.als)
of the memory model, a set of [litmus tests](alloy/tests) written in a
rudimentary syntax, [C++ source](alloy/litmus.cpp) for a tool to translate
the litmus tests to alloy, and a [makefile](alloy/Makefile) to execute the
tests. Simply run "make -j4" from the [alloy](alloy) subdirectory to run the
tests. Required dependencies are just g++ and GNU make.

