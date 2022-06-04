
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

def getvec(vec):
    valtype = vec.type.template_argument(0)
    assert(valtype.code == gdb.TYPE_CODE_PTR)
    vecstr = str(vec)
    length = vecstr.find("length ")
    if length < 0:
        raise ValueError("Unparseable printing of std::vector: {}".format(vecstr))
    lenstart = length + len("length ")
    comma = vecstr.find(",", lenstart)
    if comma < 0:
        raise ValueError("Unparseable printing of std::vector: {}".format(vecstr))
    veclen = int(vecstr[lenstart:comma])
    if veclen == 0:
        return list()
    else:
        vecstart = vecstr.find("{")
        vecend = vecstr.find("}")
        contents = vecstr[vecstart+1:vecend]
        contents = contents.split(", ")
        vec = [ gdb.Value(int(c, base=16)).cast(valtype) for c in contents ]
        return vec

def mpzToInt(mpz):
    if mpz['_mp_size'] == 0:
        return 0
    if mpz['_mp_size'] > 1:
        raise NotImplementedError("Conversion for GMP MPZ with more than one limb allocated is unimplemented")
    neg = -1 if mpz['_mp_size'] < 0 else 1
    return neg * int(mpz['_mp_d'].dereference())

def derefoper(oper):
    return oper.cast(opptrtype).dereference()

opptrtype = None
mpq_struct = None
mpz_struct = None
class ENodePrinter:
    def __init__(self, val):
        self.val = val
    def to_string(self):
        global opptrtype, OpTypeToSymbol, mpz_struct, mpq_struct
        if opptrtype is None:
            opptrtype = gdb.lookup_type('expr::Operator').pointer()
            mpz_struct = gdb.lookup_type('__mpz_struct')
            mpq_struct = gdb.lookup_type('__mpq_struct')

        args = getvec(self.val['args'])
        oper = derefoper(self.val['oper'])
        optype = oper.dynamic_type
        if optype.name.find("expr::DefOp") == 0:
            # Operator (PLUS, FAPP, etc.)
            optype = optype.template_argument(0)
            op = optype.name[len("expr::op::__"):]
            if op == "FAPP":
                fdecl = args[0].dereference()
                fname = getvec(fdecl['args'])[0].dereference()
                if len(args) == 1:
                    return str(fname)
                else:
                    args.pop(0)
                    retstr = "(" + str(fname)
                    for arg in args:
                        retstr += " " + str(arg.dereference())
                    retstr += ")"
                    return retstr
            elif op == "FDECL":
                fname = str(args[0].dereference())
                sort = str(args[-1].dereference())
                args = args[1:-1]
                retstr = "(declare-fun " + fname + " ("
                retstr += " ".join(str(arg.dereference()) for arg in args)
                retstr += ") " + sort + ")"
                return retstr
            elif op == "BIND":
                if len(args) == 2:
                    op0 = derefoper(args[0]['oper'])
                    op1 = derefoper(args[1]['oper'])
                    op0type = op0.dynamic_type
                    op1type = op1.dynamic_type
                    if "mpz_struct" in str(op0type) and "BvSort" in str(op1type):
                        val0 = op0.cast(op0type)['val'].cast(mpz_struct)
                        valint = mpzToInt(val0)
                        return "#x" + hex(valint)[2:]
                        #width = op1.cast(op1type)['val']['m_width']
                        #return "#x" + valint.to_bytes(width, 'big').hex()
            if op not in OpTypeToSymbol:
                raise ValueError("Unknown DefOp type \"{}\"".format(op))
            sym = OpTypeToSymbol[op]
            if len(args) == 0:
                return sym
            else:
                retstr = "(" + sym
                for arg in args:
                    retstr += " " + str(arg.dereference())
                retstr += ")"
                return retstr
        elif optype.name.find("expr::Terminal") == 0:
            val = oper.cast(optype)['val']
            optype = optype.template_argument(0)
            opname = str(optype)
            if "__gmp_expr" in opname:
                return str(val)
            elif "string" in opname:
                return str(val)[1:-1]
            elif "BvSort" in opname:
                # Actually a sort
                width = int(val['m_width'])
                return "(_ BitVec " + str(width) + ")"
            else:
                raise ValueError("Unknown Terminal type {}".format(optype))
        else:
            raise ValueError("Unknown Expr operator type {}".format(optype))

class ExprPrinter:
    def __init__(self, val):
        self.val = val
    def to_string(self):
        #return "ExprPrinter " + str(self.val.type)
        fields = getfields(self.val)
        if 'px' not in fields:
            raise ValueError("The Expr pretty-printer can't find the ENode*. Fields: {}".format(fields))
        return str(self.val['px'].dereference())

class MatchExprPrinter(gdb.printing.PrettyPrinter):
    def __init__(self):
        self.name = "Expr"
        self.enabled = True

    def __call__(self, val):
        if val.type.code == gdb.TYPE_CODE_REF:
            val = val.referenced_value()
        unqvaltype = val.type.unqualified()
        unqvaltype = unqvaltype.strip_typedefs()
        typename = str(unqvaltype)
        if typename == "expr::Expr" or typename == "boost::intrusive_ptr<expr::ENode>":
            return ExprPrinter(val)
        # My std::vector parsing is relying on ENode* being unparsed
        #elif typename == "expr::ENode *":
        #    return ENodePrinter(val.dereference())
        elif typename == "expr::ENode":
            return ENodePrinter(val)
        else:
            return None

intrusive_ptr = None
enode_ptr = None
expr = None
def TemplateRewriter(vtype):
    global intrusive_ptr, enode_ptr, expr
    if intrusive_ptr is None:
        intrusive_ptr = gdb.lookup_type("boost::intrusive_ptr<expr::ENode>")
        enode_ptr = gdb.lookup_type("expr::ENode").pointer()
        expr = gdb.lookup_type("expr::Expr")
    templargs = []
    n = 0
    while True:
        try:
            templargs.push_back(vtype.template_argument(n))
            n += 1
        except:
            break
    if len(templargs) == 0:
        if vtype == intrusive_ptr:
            return expr
        else:
            return vtype
    newargs = [ TemplateRewriter(ty) for ty in templargs ]
    strtype = str(vtype)
    prefix = strtype[:strtype.find("<")]
    print(prefix)
    suffix = strtype[strtype.rfind(">"):]
    print(suffix)
    newtype = prefix + ", ".join(newargs) + suffix
    newtype = gdb.lookup_type(newtype)
    return newtype

class ExprFrameDecorator(gdb.FrameDecorator.FrameDecorator):
    def frame_args(self):
        args = super().frame_args()
        for arg in args:
            if arg.val:
                print(arg.val.type)
                arg.val = arg.val.cast(TemplateRewriter(arg.val.type))
                print(arg.val.type)
            yield arg

class ExprFrameFilter():
    def __init__(self):
        self.name = "ExprFrameFilter"
        self.priority = 100
        self.enabled = True
        gdb.frame_filters[self.name] = self
    def filter(self, frame_iter):
        print("filter")
        return map(ExprFrameDecorator, frame_iter)
eff = ExprFrameFilter()

class ExprTypePrinter(gdb.types.TypePrinter):
    def __init__(self, name):
        self.enabled = True
        self.name = name
    def instantiate(self):
        global intrusive_ptr, enode_ptr, expr
        if intrusive_ptr is None:
            intrusive_ptr = gdb.lookup_type("boost::intrusive_ptr<expr::ENode>")
            enode_ptr = gdb.lookup_type("expr::ENode").pointer()
            expr = gdb.lookup_type("expr::Expr")
        return self
    def recognize(self, otype):
        global intrusive_ptr, enode_ptr
        if otype == intrusive_ptr or otype == enode_ptr:
            return "expr::Expr"
        return None

gdb.types.register_type_printer(gdb.current_objfile(), ExprTypePrinter("Expr"))
gdb.printing.register_pretty_printer(gdb.current_objfile(), MatchExprPrinter(), replace=True)
