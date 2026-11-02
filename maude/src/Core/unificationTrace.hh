/*

    Unification trace: an annotation of the inference steps of the unification
    algorithm, for extracting proof certificates. Enabled by setting the
    environment variable MAUDE_UNIFICATION_TRACE; one event per line on stderr.
    The trace observes the algorithm and never changes it.

*/
#ifndef _unificationTrace_hh_
#define _unificationTrace_hh_
#include <cstdlib>
#include <iostream>

inline bool
unificationTraceOn()
{
  static const bool on = getenv("MAUDE_UNIFICATION_TRACE") != nullptr;
  return on;
}

#define UTRACE(stuff) \
  do { if (unificationTraceOn()) std::cerr << "@u " << stuff << '\n'; } while (false)

#endif
