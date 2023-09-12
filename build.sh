opam switch create . ocaml-system --no-install
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
opam pin add -n -y coq 8.17.1

make builddep
make -j4
