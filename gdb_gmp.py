
import pdb

import gdb

def getfields(val):
    if type(val) is gdb.Value:
        intype = val.type
    elif type(val) is gdb.Type:
        intype = val
    else:
        raise TypeError("Invalid argument type for getfields")
    intype = intype.strip_typedefs()
    return tuple(f.name for f in intype.fields())

OpTypeToSymbol = {
    # Core theory
    'TRUE': 'true',
    'FALSE': 'false',
    'AND': 'and',
    'OR': 'or',
    'XOR': 'xor', # Doesn't exist?
    'NEG': 'not',
    'IMPL': '=>',
    'ITE': 'ite',
    'IFF': '<=>', # Doesn't exist?

    # Ints theory
    'PLUS': '+',
    'MINUS': '-',
    'MULT': '*',
    'DIV': '/',
    'IDIV': '/',
    'MOD': 'mod',
    'REM': 'mod', # Doesn't exist?
    'UN_MINUS': '-',
    'ABS': 'abs',
    'PINFTY': 'oo', # Doesn't exist?
    'NINFTY': '-oo', # Doesn't exist?
    'EQ': '=',
    'NEQ': 'distinct',
    'LEQ': '<=',
    'GEQ': '>=',
    'LT': '<',
    'GT': '>',

    # BitVectors theory
    'BNOT': 'bvnot',
    'BREDAND': 'bvredand',
    'BREDOR': 'bvredor',
    'BAND': 'bvand',
    'BOR': 'bvor',
    'BXOR': 'bvxor',
    'BNAND': 'bvnand',
    'BNOR': 'bvnor',
    'BXNOR': 'bvxnor',

    'BNEG': 'bvneg',
    'BADD': 'bvadd',
    'BSUB': 'bvsub',
    'BMUL': 'bvmul',
    'BUDIV': 'bvudiv',
    'BSDIV': 'bvsdiv',
    'BUREM': 'bvurem',
    'BSREM': 'bvsrem',
    'BSMOD': 'bvsmod',

    'BULT': 'bvult',
    'BSLT': 'bvslt',
    'BULE': 'bvule',
    'BSLE': 'bvsle',
    'BUGT': 'bvugt',
    'BSGT': 'bvsgt',
    'BUGE': 'bvuge',
    'BSGE': 'bvsge',

    'BSEXT': 'bvsext',
    'BZEXT': 'bvzext',
    'BREPEAT': 'bvrepeat',
    'BSHL': 'bvshl',
    'BLSHR': 'bvlshr',
    'BASHR': 'bvashr',
    'BROTATE_LEFT': 'bvrotleft',
    'BROTATE_RIGHT': 'bvrotright',
    'BEXT_ROTATE_LEFT': 'bvextrotleft',
    'BEXT_ROTATE_RIGHT': 'bvextrotright',

    'BCONCAT': 'concat',
    'BEXTRACT': 'extract',
    'INT2BV': 'int2bv',
    'BV2INT': 'bv2int',

    # Arrays theory
    'SELECT': 'select',
    'STORE': 'store',
    'CONST_ARRAY': 'as-const',
    'ARRAY_MAP': 'array-map',
    'ARRAY_DEFAULT': 'array-default',
    'AS_ARRAY': 'as-array',

    # Quantifiers
    'FORALL': 'forall',
    'EXISTS': 'exists',

    # Sorts
    'INT_TY': 'Int',
    'CHAR_TY': 'Char',
    'STRING_TY': 'String',
    'REAL_TY': 'Real',
    'BOOL_TY': 'Bool',
    'ARRAY_TY': 'Array'
}

SortOps = { 'INT_TY', 'CHAR_TY', 'STRING_TY', 'REAL_TY', 'BOOL_TY', 'ARRAY_TY' }

def mpzToInt(mpz):
    if mpz['_mp_size'] == 0:
        return 0
    if mpz['_mp_size'] > 1:
        raise NotImplementedError("Conversion for GMP MPZ with more than one limb allocated is unimplemented")
    neg = -1 if mpz['_mp_size'] < 0 else 1
    return neg * int(mpz['_mp_d'].dereference())

def mpqToFloat(mpq):
    num = mpzToInt(mpq['_mp_num'])
    den = mpzToInt(mpq['_mp_den'])
    return num / den

mpq_struct = None
mpz_struct = None
class MPZPrinter:
    def __init__(self, val):
        self.val = val
    def to_string(self):
        global mpz_struct
        return str(mpzToInt(self.val['mp']))

class MPQPrinter:
    def __init__(self, val):
        self.val = val
    def to_string(self):
        global mpq_struct
        return str(mpqToFloat(self.val['mp']))

class MatchGMPPrinter(gdb.printing.PrettyPrinter):
    def __init__(self):
        self.name = "GMPXX"
        self.enabled = True

    def __call__(self, val):
        if val.type.code == gdb.TYPE_CODE_REF:
            val = val.referenced_value()
        unqvaltype = val.type.unqualified()
        unqvaltype = unqvaltype.strip_typedefs()
        typename = str(unqvaltype)
        if "mpz_struct" in typename:
            return MPZPrinter(val)
        elif "mpq_struct" in typename:
            return MPQPrinter(val)
        else:
            return None

gdb.printing.register_pretty_printer(gdb.current_objfile(), MatchGMPPrinter(), replace=True)
