
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
        self.enabled = False
        try:
            self.mpqtype = gdb.lookup_type("mpq_class").strip_typedefs()
            self.enabled = True
        except:
            self.mpqtype = None
        try:
            self.mpztype = gdb.lookup_type("mpz_class").strip_typedefs()
            self.enabled = True
        except:
            self.mpztype = None

    def __call__(self, val):
        if val.type.code == gdb.TYPE_CODE_REF:
            val = val.referenced_value()
        unqvaltype = val.type.unqualified()
        unqvaltype = unqvaltype.strip_typedefs()
        if unqvaltype == self.mpztype:
            return MPZPrinter(val)
        elif unqvaltype == self.mpqtype:
            return MPQPrinter(val)
        else:
            return None

gdb.printing.register_pretty_printer(gdb.current_objfile(), MatchGMPPrinter(), replace=True)
