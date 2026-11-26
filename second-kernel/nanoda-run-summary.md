# Second kernel check (nanoda) on TITAN, 26 Nov 2026 (Europe/Stockholm)

Exporter: lean4export v4.34.0 tag, commit 076e8e57707e813375e8f9da8bf989799ace9680, toolchain bumped to leanprover/lean4:v4.34.1 (export meta: exporter 3.1.0, format 3.1.0, lean githash 5045d0056413266e57c625dcd7c365b10e377c52)
Command (in openai/math project root with ListDistinct.olean built):
  lake env lean4export.exe ListDistinct -- ListDistinctExposition.circuit_lower ListDistinctExposition.manyList_unfolded ListDistinctExposition.manyList_full_unfolded ListDistinctExposition.upper ListDistinctExposition.tagged_hard > circuit_lower.ndjson
Export: started 20:14:59 CET, exit 0, 43.7 s, 462,908,674 bytes, SHA256 E5390FA99306D47FF6C0849B267BA33D5851FE70D2A7967238EF7074069A7D04
Export contains Processor.hard_of_descent, Tagged.manyList_of_tag and 148 lines naming BatchDescent components (names are interned, so counted by component).

Checker: nanoda_lib 0.4.32, commit 0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929 (7 Nov 2026), built with cargo +stable-x86_64-pc-windows-gnu --release (MSVC link.exe absent on TITAN)
Config: num_threads 4, stack 1 GiB, permitted_axioms [propext, Classical.choice, Quot.sound], unpermitted_axiom_hard_error false, nat_extension true, string_extension true, pp ListDistinctExposition.circuit_lower
Run: started 20:18:20 CET, exit 0, 19.9 s, output "Checked 45579 declarations with no errors"
Pretty printed type of circuit_lower matches the statement in the paper.
Negative control: same export with permitted_axioms [propext, Quot.sound] (Classical.choice removed): panics "declaration Classical.arbitrary depends on Classical.choice which was not found in the environment", exit 101, 6.2 s.
Priority: BelowNormal for all processes.
