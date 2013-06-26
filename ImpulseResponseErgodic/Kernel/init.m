(* Mathematica Init File *)

PrependTo[$Path,"g:/git/umbralCalculus"]
PrependTo[$Path,"G:/git/MatPert"]

PrependTo[$Path,"g:/git/mathAMA/NumericAMA"]

PrependTo[$Path,"g:/git/mathAMA/SymbolicAMA"]
PrependTo[$Path,"g:/git/ProjectionMethodTools/ProjectionMethodTools"]
(*Needs["ProjectionMethodTools`"]*)
Get[ "ImpulseResponseErgodic`ImpulseResponseErgodic`"]

Print[{Directory[],$Path}]
Print["done reading init.m in Impres`impres`Kernel"]