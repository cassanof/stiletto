SNAKE_EXT=stile
UNAME := $(shell uname)
ifeq ($(UNAME), Linux)
  NASM_FORMAT=elf64
  CLANG_FLAGS=-mstackrealign -m64 -g -fstack-protector-all -Wstack-protector -fno-omit-frame-pointer
else
ifeq ($(UNAME), Darwin)
  NASM_FORMAT=macho64
  CLANG_FLAGS=-mstackrealign -m64 -g -fstack-protector-all -Wstack-protector -fno-omit-frame-pointer -arch x86_64
endif
endif

PKGS=ounit2,extlib,unix
BUILD=ocamlbuild -r -use-ocamlfind -cflag -annot -ocamlyacc 'ocamlyacc -v'

main: *.ml parser.mly lexer.mll
	$(BUILD) -package $(PKGS) main.native
	mv main.native main

test: *.ml parser.mly lexer.mll main
	$(BUILD) -package $(PKGS) test.native
	mv test.native test

output/%.run: output/%.o main.c gc.c
	clang $(CLANG_FLAGS) -o $@ gc.c main.c $<

output/%.o: output/%.s
	nasm -f $(NASM_FORMAT) -o $@ $<

.PRECIOUS: output/%.s
output/%.s: input/%.$(SNAKE_EXT) main
	./main $< > $@

output/do_pass/%.run: output/do_pass/%.o main.c gc.c
	clang $(CLANG_FLAGS) -o $@ gc.c main.c $<

output/do_pass/%.o: output/do_pass/%.s
	nasm -f $(NASM_FORMAT) -o $@ $<

.PRECIOUS: output/do_pass/%.s
output/do_pass/%.s: input/do_pass/%.$(SNAKE_EXT) main
	./main $< > $@


output/dont_pass/%.run: output/dont_pass/%.o main.c gc.c
	clang -g $(CLANG_FLAGS) -o $@ gc.c main.c $<

output/dont_pass/%.o: output/dont_pass/%.s
	nasm -f $(NASM_FORMAT) -o $@ $<

.PRECIOUS: output/dont_pass/%.s
output/dont_pass/%.s: input/dont_pass/%.$(SNAKE_EXT) main
	./main $< > $@


output/do_err/%.run: output/do_err/%.o main.c gc.c
	clang $(CLANG_FLAGS) -o $@ gc.c main.c $<

output/do_err/%.o: output/do_err/%.s
	nasm -f $(NASM_FORMAT) -o $@ $<

.PRECIOUS: output/do_err/%.s
output/do_err/%.s: input/do_err/%.$(SNAKE_EXT) main
	./main $< > $@


output/dont_err/%.run: output/dont_err/%.o main.c gc.c
	clang -g $(CLANG_FLAGS) -o $@ gc.c main.c $<

output/dont_err/%.o: output/dont_err/%.s
	nasm -f $(NASM_FORMAT) -o $@ $<

.PRECIOUS: output/dont_err/%.s
output/dont_err/%.s: input/dont_err/%.$(SNAKE_EXT) main
	./main $< > $@

gctest.o: gctest.c gc.h
	gcc gctest.c -m64 -c -g -o gctest.o

# gc.o: gc.c gc.h
# 	gcc gc.c -m64 -c -g -o gc.o

# cutest-1.5/CuTest.o: cutest-1.5/CuTest.c cutest-1.5/CuTest.h
# 	gcc -m32 cutest-1.5/CuTest.c -c -g -o cutest-1.5/CuTest.o

# gctest: gctest.o gc.c cutest-1.5/CuTest.o cutest-1.5/CuTest.h
# 	gcc -m32 cutest-1.5/AllTests.c cutest-1.5/CuTest.o gctest.o gc.c -o gctest


clean:
	rm -rf output/*.o output/*.s output/*.dSYM output/*.run *.log *.o
	rm -rf output/*/*.o output/*/*.s output/*/*.dSYM output/*/*.run
	rm -rf _build/
	rm -f main test
