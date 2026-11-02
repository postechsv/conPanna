#!/bin/bash
# Build the instrumented Maude in this directory (conPanna addition, not upstream).
#
#   maude/build.sh            # binary: maude/Opt/src/Main/maude
#
# Needs a C++ compiler, flex, bison, autoconf, automake and GMP with its C++ headers
# (gmpxx.h). libsigsegv, BuDDy and Tecla are built locally into maude/.deps; nothing is
# installed system-wide. Run the binary with MAUDE_LIB=maude/src/Main so that it finds
# prelude.maude; set MAUDE_UNIFICATION_TRACE=1 to get the unification trace on stderr.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
DEPS=$HERE/.deps
OPT=$DEPS/opt
JOBS=${JOBS:-$(nproc)}
mkdir -p "$DEPS/src" "$OPT"

fetch() { [ -f "$DEPS/src/$(basename "$1")" ] || curl -sSLf -o "$DEPS/src/$(basename "$1")" "$1"; }

if [ ! -f "$OPT/lib/libsigsegv.a" ]; then
  fetch https://ftp.gnu.org/gnu/libsigsegv/libsigsegv-2.15.tar.gz
  (cd "$DEPS/src" && tar xf libsigsegv-2.15.tar.gz && mkdir -p libsigsegv-2.15/Opt && cd libsigsegv-2.15/Opt &&
   ../configure CFLAGS="-g -fno-stack-protector -O3" --prefix="$OPT" --enable-shared=no >/dev/null &&
   make -j"$JOBS" >/dev/null && make install >/dev/null)
fi
if [ ! -f "$OPT/lib/libbdd.a" ]; then
  fetch https://github.com/utwente-fmt/buddy/releases/download/v2.4/buddy-2.4.tar.gz
  (cd "$DEPS/src" && tar xf buddy-2.4.tar.gz && mkdir -p buddy-2.4/Opt && cd buddy-2.4/Opt &&
   ../configure LDFLAGS=-lm CFLAGS="-g -fno-stack-protector -O3" CXXFLAGS="-g -fno-stack-protector -O3" \
     --prefix="$OPT" --disable-shared >/dev/null &&
   make -j"$JOBS" >/dev/null && make install >/dev/null)
fi
if [ ! -f "$OPT/lib/libtecla.a" ]; then
  fetch https://sites.astro.caltech.edu/~mcs/tecla/libtecla-1.6.3.tar.gz
  (cd "$DEPS/src" && tar xf libtecla-1.6.3.tar.gz && cd libtecla &&
   ./configure CFLAGS="-g -fno-stack-protector -O3" --prefix="$OPT" >/dev/null &&
   make >/dev/null; make install >/dev/null)
fi
# link statically against the local libraries
mkdir -p "$OPT/lib/Hidden" && find "$OPT/lib" -maxdepth 1 -name "*.so*" -exec mv {} "$OPT/lib/Hidden/" \;

cd "$HERE"
[ -f configure ] || autoreconf -i >/dev/null 2>&1
mkdir -p Opt && cd Opt
[ -f Makefile ] || ../configure --with-smt=no CXXFLAGS="-g -O2 -fno-stack-protector" \
  CPPFLAGS="-I$OPT/include" LDFLAGS="-L$OPT/lib" >/dev/null
make -j"$JOBS" >/dev/null
echo "built $HERE/Opt/src/Main/maude"
