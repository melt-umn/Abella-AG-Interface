
all: bools.thc nats.thc integers.thc integer_addition.thc integer_multiplication.thc \
     integer_division.thc integer_comparison.thc pairs.thc lists.thc strings.thc attr_val.thc


# All the *.out files are just the output from Abella as it processes
# the file.  You shouldn't ever need to see this (just load up the
# file in Emacs and use Proof General), but we'll keep it around after
# the compilation anyway in case it is needed for something.

bools.thc: bools.thm
	abella bools.thm -c bools.thc -o bools.out

nats.thc: nats.thm
	abella nats.thm -c nats.thc -o nats.out

integers.thc: integers.thm bools.thc nats.thc
	abella integers.thm -c integers.thc -o integers.out

integer_addition.thc: integer_addition.thm integers.thc
	abella integer_addition.thm -c integer_addition.thc -o integer_addition.out

integer_multiplication.thc: integer_multiplication.thm integer_addition.thc
	abella integer_multiplication.thm -c integer_multiplication.thc -o integer_multiplication.out

integer_division.thc: integer_division.thm integer_multiplication.thc
	abella integer_division.thm -c integer_division.thc -o integer_division.out

integer_comparison.thc: integer_comparison.thm integer_multiplication.thc
	abella integer_comparison.thm -c integer_comparison.thc -o integer_comparison.out

pairs.thc: pairs.thm
	abella pairs.thm -c pairs.thc -o pairs.out

lists.thc: lists.thm
	abella lists.thm -c lists.thc -o lists.out

strings.thc: strings.thm lists.thc
	abella strings.thm -c strings.thc -o strings.out

attr_val.thc: attr_val.thm
	abella attr_val.thm -c attr_val.thc -o attr_val.out


#remove unnecessary generated files
part-clean:
	rm *.out *~

#remove all generated files
clean:
	rm *.thc *.out *~
