# Vulkan-MemoryModel

The Vulkan-MemoryModel repo includes documentation and tools related to the
Vulkan Memory Model that are not built into the core specification. The core
specification is available at
https://www.khronos.org/registry/vulkan/specs/1.1-extensions/html/vkspec.html#VK_KHR_vulkan_memory_model.
Other Khronos-maintained specifications and software projects that have been
extended to support this model are listed in the
[extension release checklist](https://github.com/KhronosGroup/Vulkan-Docs/issues/787).

## Alloy Model

The [alloy](alloy) subdirectory includes an
[Alloy](http://alloy.lcs.mit.edu/alloy/index.html) [implementation](alloy/spirv.als)
of the memory model, a set of [litmus tests](alloy/tests) written in a
rudimentary syntax, [C++ source](alloy/litmus.cpp) for a tool to translate
the litmus tests to alloy, and a [makefile](alloy/Makefile) to execute the
tests. A java class to run the alloy tests is compiled against
https://oss.sonatype.org/content/repositories/snapshots/org/alloytools/org.alloytools.alloy.dist/5.0.0-SNAPSHOT/org.alloytools.alloy.dist-5.0.0-20190619.101010-34.jar.
Download this jar file and place it in the [alloy](alloy) subdirectory.
Simply run "make -j4" from the [alloy](alloy) subdirectory to run the
tests. Required dependencies are just g++, GNU make, alloy, and a Java runtime.

## License

This repo is treated as an offshoot of the Vulkan-Docs repo, and uses the
same Creative Commons Attribution 4.0 license. See [COPYING.md](COPYING.md).

[Alloy](http://alloy.lcs.mit.edu/alloy/index.html) is a third-party tool
used in this repo, and is available from
https://github.com/AlloyTools/org.alloytools.alloy.