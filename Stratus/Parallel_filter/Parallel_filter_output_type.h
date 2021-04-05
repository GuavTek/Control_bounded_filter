#ifndef Parallel_filter_OUTPUT_DT_SC_WRAPPER_TYPE
#define Parallel_filter_OUTPUT_DT_SC_WRAPPER_TYPE 1

#include "cynw_memory.h"
#include "FloatType.h"

struct Parallel_filter_OUTPUT_DT
{
    //
    // Member declarations.
    //
    floatType Result;
    
    //
    // Default constructor.
    //
    Parallel_filter_OUTPUT_DT()
    {
    }
    
    //
    // Copy constructor.
    //
    Parallel_filter_OUTPUT_DT( const Parallel_filter_OUTPUT_DT& other )
    {
        Result = other.Result;
    }
    
    //
    // Comparison operator.
    //
    inline bool operator == ( const Parallel_filter_OUTPUT_DT& other )
    {
        if ( !(Result == other.Result) )
            return false;
        return true;
    }
    
    //
    // Assignment operator from Parallel_filter_OUTPUT_DT.
    //
    inline Parallel_filter_OUTPUT_DT& operator = ( const Parallel_filter_OUTPUT_DT& other )
    {
        Result = other.Result;
        return *this;
    }
    
};
//
// sc_trace function.
//
inline void sc_trace( sc_trace_file* tf, const Parallel_filter_OUTPUT_DT& object, const std::string& in_name )
{
    if (tf)
    {
        tf->trace( object.Result.raw_bits(), in_name + std::string(".Result"));
    }
}

//
// stream operator.
//
inline ostream & operator << ( ostream & os, const Parallel_filter_OUTPUT_DT& object )
{
#ifndef STRATUS_HLS
    os << "(";
    os <<  object.Result;
    os << ")";
#endif
    return os;
}


template <>
struct cynw_sc_wrap< Parallel_filter_OUTPUT_DT >
{
    typedef Parallel_filter_OUTPUT_DT spec;
    typedef Parallel_filter_OUTPUT_DT sc;
};
#endif


