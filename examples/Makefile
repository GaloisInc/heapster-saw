all: Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

include Makefile.coq

%.bc: %.c
	clang -emit-llvm -g -c $<

linked_list.v: linked_list.bc linked_list.saw linked_list.sawcore
	stack exec saw linked_list.saw

xor_swap.v: xor_swap.bc xor_swap.saw
	stack exec saw xor_swap.saw

xor_swap_rust.bc: xor_swap_rust.rs
	rustc --emit=llvm-bc xor_swap_rust.rs

xor_swap_rust.v: xor_swap_rust.bc xor_swap_rust.saw
	stack exec saw xor_swap_rust.saw

string_set.v: string_set.bc string_set.saw string_set.sawcore
	stack exec saw string_set.saw

loops.v: loops.bc loops.saw loops.sawcore
	stack exec saw loops.saw

arrays.v: arrays.bc arrays.saw arrays.sawcore
	stack exec saw arrays.saw

iter_linked_list.v: iter_linked_list.bc iter_linked_list.saw iter_linked_list.sawcore
	stack exec saw iter_linked_list.saw
