#ifndef __EXPR_BV__HH_
#define __EXPR_BV__HH_

/** Bit-Vector expressions
 
 * This file is included from middle of Expr.hpp
 */
namespace expr
{
  namespace op
  {
    namespace bv
    {
      struct BvSort
      {
        unsigned m_width;
        BvSort (unsigned width) : m_width (width) {}
        BvSort (const BvSort &o) : m_width (o.m_width) {}
        
        bool operator< (const BvSort &b) const { return m_width < b.m_width; }
        bool operator== (const BvSort &b) const { return m_width == b.m_width; }
        bool operator!= (const BvSort &b) const { return m_width != b.m_width; }

        size_t hash () const
        {
          std::hash<unsigned> hasher;
          return hasher (m_width);
        }

        void Print (std::ostream &OS) const { OS << "bv(" << m_width << ")"; }
      };
      inline std::ostream &operator<< (std::ostream &OS, const BvSort &b)
      {
        b.Print (OS);
        return OS;
      }
    }
  }

  template<> struct TerminalTrait<const op::bv::BvSort>
  {
    typedef const op::bv::BvSort value_type;
    static inline void print (std::ostream &OS,
                              const op::bv::BvSort &b,
                              int depth, bool brkt) { OS << b; }
    static inline bool less (const op::bv::BvSort &b1,
                             const op::bv::BvSort &b2)
    { return b1 < b2; }
    static inline bool equal_to (const op::bv::BvSort &b1,
                                 const op::bv::BvSort &b2)
    { return b1 == b2; }
    static inline size_t hash (const op::bv::BvSort &b)
    { return b.hash (); }
  };

  typedef Terminal<const bv::BvSort> BVSORT;

  namespace op
  {
    NOP_BASE(BvBoolOp)
    NOP(BNOT,"bvnot",FUNCTIONAL,BvBoolOp)
    NOP(BREDAND,"bvredand",FUNCTIONAL,BvBoolOp)
    NOP(BREDOR,"bvredor",FUNCTIONAL,BvBoolOp)
    NOP(BAND,"bvand",FUNCTIONAL,BvBoolOp)
    NOP(BOR,"bvor",FUNCTIONAL,BvBoolOp)
    NOP(BXOR,"bvxor",FUNCTIONAL,BvBoolOp)
    NOP(BNAND,"bvnand",FUNCTIONAL,BvBoolOp)
    NOP(BNOR,"bvnor",FUNCTIONAL,BvBoolOp)
    NOP(BXNOR,"bvxnor",FUNCTIONAL,BvBoolOp)

    NOP_BASE(BvNumericOp)
    NOP(BNEG,"bvneg",FUNCTIONAL,BvNumericOp)
    NOP(BADD,"bvadd",FUNCTIONAL,BvNumericOp)
    NOP(BSUB,"bvsub",FUNCTIONAL,BvNumericOp)
    NOP(BMUL,"bvmul",FUNCTIONAL,BvNumericOp)
    NOP(BUDIV,"bvudiv",FUNCTIONAL,BvNumericOp)
    NOP(BSDIV,"bvsdiv",FUNCTIONAL,BvNumericOp)
    NOP(BUREM,"bvurem",FUNCTIONAL,BvNumericOp)
    NOP(BSREM,"bvsrem",FUNCTIONAL,BvNumericOp)
    NOP(BSMOD,"bvsmod",FUNCTIONAL,BvNumericOp)

    NOP(BSHL,"bvshl",FUNCTIONAL,BvNumericOp)
    NOP(BLSHR,"bvlshr",FUNCTIONAL,BvNumericOp)
    NOP(BASHR,"bvashr",FUNCTIONAL,BvNumericOp)
    NOP(BROTATE_LEFT,"bvrotleft",FUNCTIONAL,BvNumericOp)
    NOP(BROTATE_RIGHT,"bvrotright",FUNCTIONAL,BvNumericOp)
    NOP(BEXT_ROTATE_LEFT,"bvextrotleft",FUNCTIONAL,BvNumericOp)
    NOP(BEXT_ROTATE_RIGHT,"bvextrotright",FUNCTIONAL,BvNumericOp)

    NOP_BASE(BvComparissonOp)
    NOP(BULT,"bvult",FUNCTIONAL,BvComparissonOp)
    NOP(BSLT,"bvslt",FUNCTIONAL,BvComparissonOp)
    NOP(BULE,"bvule",FUNCTIONAL,BvComparissonOp)
    NOP(BSLE,"bvsle",FUNCTIONAL,BvComparissonOp)
    NOP(BUGE,"bvuge",FUNCTIONAL,BvComparissonOp)
    NOP(BSGE,"bvsge",FUNCTIONAL,BvComparissonOp)
    NOP(BUGT,"bvugt",FUNCTIONAL,BvComparissonOp)
    NOP(BSGT,"bvsgt",FUNCTIONAL,BvComparissonOp)

    NOP_BASE(BvWidthOp)
    NOP(BCONCAT,"concat",FUNCTIONAL,BvWidthOp)
    NOP(BEXTRACT,"extract",FUNCTIONAL,BvWidthOp)
    NOP(BSEXT,"bvsext",FUNCTIONAL,BvWidthOp)
    NOP(BZEXT,"bvzext",FUNCTIONAL,BvWidthOp)
    NOP(BREPEAT,"bvrepeat",FUNCTIONAL,BvWidthOp)

    NOP_BASE(BvMiscOp)
    NOP(INT2BV,"int2bv",FUNCTIONAL,BvMiscOp)
    NOP(BV2INT,"bv2int",FUNCTIONAL,BvMiscOp)

    /// true if v is a bit-vector numeral
    inline bool is_bvnum (Expr v)
    {
      return isOpX<BIND> (v) && v->arity () == 2 &&
      isOpX<MPZ> (v->arg (0)) && isOpX<BVSORT> (v->arg (1));
    }

    /// true if v is a bit-vector variable
    inline bool is_bvconst (Expr v)
    {
      return isOpX<FAPP> (v) &&
      isOpX<FDECL> (v->first()) && v->first()->arity () == 2 &&
      isOpX<BVSORT> (v->first()->arg (1));
    }

    /// true if v is a bit-vector variable
    inline bool is_bvvar (Expr v)
    {
      return isOpX<BIND> (v) && v->arity () >= 2 &&
      !isOpX<MPZ> (v->left()) && isOpX<BVSORT> (v->right());
    }

    /// true if v is a bit-vector operator
    inline bool is_bvop (Expr v)
    {
      return isOp<BvBoolOp> (v) || isOp<BvComparissonOp> (v) ||
      isOp<BvNumericOp> (v) || isOp<BvMiscOp> (v) || isOp<BvWidthOp> (v);
    }

    /// true if v is in the bit-vector sort (is a const, var, or operator)
    inline bool is_bv (Expr v)
    {
      return is_bvop(v) || is_bvconst(v) || is_bvvar(v) || is_bvnum(v);
    }

    namespace bv
    {
      inline Expr bvsort (unsigned width, ExprFactory &efac)
      {return mkTerm<const BvSort> (BvSort (width), efac);}

      inline unsigned width (Expr bvsort)
      {return getTerm<const BvSort>(bvsort).m_width;}

      /// Bit-vector numeral of a given sort
      /// num is an integer numeral, and bvsort is a bit-vector sort
      inline Expr bvnum (Expr num, Expr bvsort)
      {return bind::bind (num, bvsort);}

      inline Expr bvnum (mpz_class num, Expr bvsort)
      {return bind::bind (mkTerm(num, bvsort->efac()), bvsort);}

      /// bit-vector numeral of an arbitrary precision integer
      inline Expr bvnum (mpz_class num, unsigned bwidth, ExprFactory &efac)
      {return bvnum (mkTerm (num, efac), bvsort (bwidth, efac));}

      inline mpz_class toMpz (Expr v)
      {
        assert (is_bvnum (v));
        return getTerm<mpz_class> (v->arg (0));
      }

      inline Expr bvConst (Expr v, unsigned width)
      {
        Expr sort = bvsort (width, v->efac ());
        return bind::mkConst (v, sort);
      }

      /* XXX Add helper methods as needed */

      inline Expr bvnot (Expr v) {return mk<BNOT> (v);}

      inline Expr extract (unsigned high, unsigned low, Expr v)
      {
        //        assert (high > low);
        return mk<BEXTRACT> (mkTerm<unsigned> (high, v->efac ()),
                             mkTerm<unsigned> (low, v->efac ()), v);
      }

      /// high bit to extract
      inline unsigned high (Expr v) {return getTerm<unsigned> (v->arg (0));}
      /// low bit to extract
      inline unsigned low (Expr v) {return getTerm<unsigned> (v->arg (1));}
      /// bv argument to extract
      inline Expr earg (Expr v) {return v->arg (2);}

      inline Expr sext (Expr v, unsigned width)
      {return mk<BSEXT> (v, bvsort (width, v->efac ()));}

      inline Expr zext (Expr v, unsigned width)
      {return mk<BZEXT> (v, bvsort (width, v->efac ()));}

    }
    namespace bind
    {
      class IsVVar : public std::unary_function<Expr,bool>
      {
      public:
        bool operator () (Expr e)
        {
          return isIntVar(e) || isRealVar(e) || isBoolVar(e) || is_bvvar(e) || isVar<ARRAY_TY> (e);
        }
      };
    }
  }
}


#endif /*  __EXPR_BV__HH_ */
