#!/bin/bash

set -e

# Step1: generate Makefile
coq_makefile -f _CoqProject -o Makefile

# Step2: compile Coq project
make
echo -e "✅ Coq formalization compiled successfully"

# Step3: init Dune project
cd src
dune init proj ocaml_try

# Step4: Copy OCaml related files
cp -r ./ocaml/{extraction,hiparser} ./ocaml_try/
cp ./ocaml/{dune,generate_lofir.ml,nodehelper.ml,pair2string.ml,printfir_pair.ml,printfir.ml,transfast.ml,transhiast_without_inline.ml,transhiast.ml} ./ocaml_try/

# Step5: build OCaml project
cd ocaml_try
sed -i.bak '18s/.*/[]/' ./extraction/Semantics.ml
dune build
echo -e "✅ OCaml implementation built"
echo -e "🚀 Running demo on sample circuit..."

# Step6: run test
./_build/default/generate_lofir.exe ../ocaml/demo/chiselbook/FormalSimple.fir
echo -e "🎉 Smoke test completed successfully!"
