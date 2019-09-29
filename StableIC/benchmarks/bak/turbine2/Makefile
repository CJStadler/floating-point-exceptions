NAME = ex6
CLANG = clang -emit-llvm
LLVMOPT = opt
OPTFLAGS = -instcombine
CXXFLAGS = -Xclang -disable-O0-optnone -ffast-math
LLVMLINK = llvm-link

NONOPT = \
    $(NAME).c\
    Random.c\
    Main.c\

OPT = \
    $(NAME)_ic.c

IR = $(NONOPT:.c=.bc)
IROPT = $(OPT:.c=.opt.bc)


%.bc: %.c
	$(CLANG) -c -o $@ $<

%.opt.bc: %.c
	$(CLANG) $(CXXFLAGS) -c -o $*.bc $<
	$(LLVMOPT) $(OPTFLAGS) $*.bc -o $@

all:  $(IR) $(IROPT)
	$(LLVMLINK) $(IROPT) $(IR) -o $(NAME)_test.bc
	llc -filetype=obj $(NAME)_test.bc
	clang $(NAME)_test.bc

clean:
	/bin/rm -f *.o *.bc *.out
