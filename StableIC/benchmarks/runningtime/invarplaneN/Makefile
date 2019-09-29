NAME = ex6
CLANG = clang++ -emit-llvm -std=c++11
LLVMOPT = opt
OPTFLAGS = -instcombine
CXXFLAGS = -Xclang -disable-O0-optnone 
LLVMLINK = llvm-link

NONOPT = \
    $(NAME).c\
    Main.c\

OPT = \
    $(NAME)_ic.c

IR = $(NONOPT:.c=.bc)
IROPT = $(OPT:.c=.opt.bc)


%.bc: %.c
	$(CLANG) $(CXXFLAGS) -g -c -o $@ $<
	$(LLVMOPT) $(OPTFLAGS) $*.bc -o $@

%.opt.bc: %.c
	$(CLANG) $(CXXFLAGS) -ffast-math -g -c -o $*.bc $<
	$(LLVMOPT) $(OPTFLAGS)  $*.bc -o $@

all:  $(IR) $(IROPT)
	$(LLVMLINK) $(IROPT) $(IR) -o $(NAME)_test.bc
	llc -filetype=obj $(NAME)_test.bc
	clang++ -lmpfr $(NAME)_test.bc

clean:
	/bin/rm -f *.o *.bc *.out
