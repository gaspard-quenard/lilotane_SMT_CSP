
# Makefile for building Lilotane as an IPASIR application
# (see github.com/biotomas/ipasir )

TARGET=$(shell basename "`pwd`")
IPASIRSOLVER ?= glucose4

all:
	mkdir -p build
	cd build && cmake .. -DCMAKE_BUILD_TYPE=DEBUG -DIPASIRSOLVER=$(IPASIRSOLVER) -DIPASIRDIR=lib && make && cp lilotane .. && cd ..

clean:
	rm -rf $(TARGET) build/
