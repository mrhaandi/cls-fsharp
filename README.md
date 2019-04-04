# (CL)S-F# 
Implementation of the Combinatory Logic Synthesizer algorithm in F#. 

## Theory

(CL)S-F# is based on inhabitant search in combinatory logic with intersection types with constructors.
In particular, given a set of typed combinators Γ and a type τ, (CL)S-F# enumerates applicative terms, built from combinators in Γ, that can be assigned the type τ.
For a detailed theoretical backround see Section 4.1 in the [PhD thesis by Andrej Dudenhefner](https://ls14-www.cs.tu-dortmund.de/cms/en/staffpages/dudenhefner/publications/index.php).

## Usage

The Visual Studio 2017 solution file `cls-fsharp.sln` contains the `cls-fsharp-core` project (synthesis algorithm) together with the `cls-fsharp-experiments` project (examples).

The `cls-fsharp-core` project is a Visual Studio 2017 `Library` and can be used independently from the main solution.
Inhabitants are constructed by first using the method `getAllInhabitants` that, given a set of typed combinators Γ and a type τ, constructs a `TreeGrammar` G spanning the set of applicative terms M, built from combinators in Γ, such that M can be assigned the type τ.
Particular terms can be enumerated using the method `listMinimalCombinatorTerms` from G.

The `cls-fsharp-experiments` project is a Visual Studio 2017 `Exe` and, provided the library, can be compiled and executed.
It demonstrates individual library features in functional program synthesis, object-oriented program synthesis, and process synthesis scenarios.
