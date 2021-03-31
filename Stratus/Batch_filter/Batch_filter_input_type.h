#ifndef Batch_filter_INPUT_DT_SC_WRAPPER_TYPE
#define Batch_filter_INPUT_DT_SC_WRAPPER_TYPE 1

#include "cynw_memory.h"

struct Batch_filter_INPUT_DT
{
    //
    // Member declarations.
    //
    sc_uint< 1 > Samples[3];
    
    typedef sc_uint< 3 > raw_type;
    
    //
    // Default constructor.
    //
    Batch_filter_INPUT_DT()
    {
        CYN_FLATTEN(Samples);
    }
    
    //
    // Copy constructor.
    //
    Batch_filter_INPUT_DT( const Batch_filter_INPUT_DT& other )
    {
        CYN_FLATTEN(Samples);
        {
            for ( int i0=0; i0 < 3; i0++ ) {
                Samples[i0] = other.Samples[i0];
            }
        }
    }
    
    //
    // Comparison operator.
    //
    inline bool operator == ( const Batch_filter_INPUT_DT& other )
    {
        {
            for ( int i0=0; i0 < 3; i0++ ) {
                if ( !(Samples[i0] == other.Samples[i0]) )
                    return false;
            }
        }
        return true;
    }
    
    //
    // Assignment operator from Batch_filter_INPUT_DT.
    //
    inline Batch_filter_INPUT_DT& operator = ( const Batch_filter_INPUT_DT& other )
    {
        {
            for ( int i0=0; i0 < 3; i0++ ) {
                Samples[i0] = other.Samples[i0];
            }
        }
        return *this;
    }
    
};
//
// sc_trace function.
//
inline void sc_trace( sc_trace_file* tf, const Batch_filter_INPUT_DT& object, const std::string& in_name )
{
    if (tf)
    {
        {
            for ( int i0=0; i0 < 3; i0++ ) {
                std::stringstream ss_out;
                ss_out << in_name << ".Samples" << "(" << i0 << ")" << std::ends;
                tf->trace( object.Samples[i0], std::string( ss_out.str() ));
            }
        }
    }
}

//
// stream operator.
//
inline ostream & operator << ( ostream & os, const Batch_filter_INPUT_DT& object )
{
#ifndef STRATUS_HLS
    os << "(";
    {
        os << "(";
        for ( int i0=0; i0 < 3; i0++ ) {
            os << " " << object.Samples[i0];
        }
        os << ")";
    }
    os << ")";
#endif
    return os;
}

//
// cynw_interpret function to generate a flat vector.
//
inline void cynw_interpret ( Batch_filter_INPUT_DT& from, Batch_filter_INPUT_DT::raw_type& to )
{
    to = (
                from.Samples[0],
                from.Samples[1],
                from.Samples[2]
                );
}

//
// cynw_interpret function to generate a Batch_filter_INPUT_DT from a flat vector.
//
inline void cynw_interpret ( const Batch_filter_INPUT_DT::raw_type& from, Batch_filter_INPUT_DT& to )
{
    cynw_interpret( (sc_uint<1>)from.range( 2,2 ), to.Samples[0] );
    cynw_interpret( (sc_uint<1>)from.range( 1,1 ), to.Samples[1] );
    cynw_interpret( (sc_uint<1>)from.range( 0,0 ), to.Samples[2] );
}


template <>
struct cynw_sc_wrap< Batch_filter_INPUT_DT >
{
    typedef Batch_filter_INPUT_DT spec;
    typedef Batch_filter_INPUT_DT sc;
};
#endif


