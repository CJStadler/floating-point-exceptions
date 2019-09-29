NAME = ex6
CLANG = clang++ -emit-llvm -std=c++11
LLVMOPT = opt
OPTFLAGS = -instcombine
CXXFLAGS = -Xclang -disable-O0-optnone -ffast-math
LLVMLINK = llvm-link

NONOPT = \
    $(NAME).cpp\
    theta.cpp\
    Main.cpp\

OPT = \
    $(NAME)_ic.cpp

IR = $(NONOPT:.cpp=.bc)
IROPT = $(OPT:.cpp=.opt.bc)


%.bc: %.cpp
	$(CLANG) -g -c -o $@ $<

%.opt.bc: %.cpp
	$(CLANG) $(CXXFLAGS) -g -c -o $*.bc $<
	$(LLVMOPT) $(OPTFLAGS) $*.bc -o $@

all:  $(IR) $(IROPT)
	$(LLVMLINK) $(IROPT) $(IR) -o $(NAME)_test.bc
	llc -filetype=obj $(NAME)_test.bc
	clang++  -lmpfr $(NAME)_test.bc

clean:
	/bin/rm -f *.o *.bc *.out
