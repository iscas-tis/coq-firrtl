Coq-Firrtl
==========
Formalizing Firrtl language in Coq.

FIRRTL is an intermediary language to describe hardware circuits. It allows some variation, from HiFIRRTL including a few higher-level constructs, e.g. case distinctions through “when” statements and aggregate data types, to LoFIRRTL, which can almost directly be mapped to a netlist. While there are existing LoFIRRTL semantics, more or less formal ones, the official  documentation only provides an informal, textual description of the HiFIRRTL semantics. The reference implementation provides a kind of formal semantics through a translation from HiFIRRTL to LoFIRRTL. In discussions within our FIRRTL verified compiler working group, we formed several ideas for mathematically sound HiFIRRTL semantics.
One difficulty with HiFIRRTL semantics is an allowed form of underspecification: in a module, one does not need to indicate all signal widths; the compiler is then supposed to find the smallest signal width that will not lead to data loss. Also, it is allowed to leave undetermined whether a reset wire shall be synchronous (i.e. resets will happen only at a rising clock edge) or asynchronous (i.e. resets will happen immediately when the reset wire gets high). When underspecified components are connected with fully specified ones, the underspecification is resolved. It is an error if components with inconsistent reset types are connected. This also shows that it is difficult to make the semantics fully compositional: some parts of the semantics are determined by the context of a component.
We earlier tried to define a semantics along the following lines: underspecified components do not get a single semantic interpretation, but a set of possibilities. During the InferWidths pass of the compiler, the widths are then determined, leading to a circuit with a unique semantic interpretation, which is the possibility with the smallest signal widths. 
The basic idea is to create a connection summary, that is a function describing all combinatorial connections in the module, and then iterate this function until a fixed point is reached. If no fixed point exists, the module is erroneous.

Installation
============
To compile the Coq formalization, the following packages are required.

* [Coq](https://coq.inria.fr) 8.13.1 or 8.15.0 
* [MathComp](https://github.com/math-comp/math-comp) 1.15.0

