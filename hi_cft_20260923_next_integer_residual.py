"""Exact biquadratic sparse residuals after clearing common denominators."""
from collections import OrderedDict
from fractions import Fraction
from math import gcd

MAX_DEN_BITS = 32768
MAX_STATES = 20000


class Limit(Exception):
    pass


def lcm(a,b):
    value = (a//gcd(a,b))*b
    if value.bit_length() > MAX_DEN_BITS:
        raise Limit('Residual common denominator exceeds32768bits')
    return value


def multiply(a,b):
    x,y,z,w = a
    e,f,g,h = b
    if not (y or z or w):
        return x*e,x*f,x*g,x*h
    if not (f or g or h):
        return x*e,y*e,z*e,w*e
    return (x*e+13*y*f-3*z*g-39*w*h,
            x*f+y*e-3*z*h-3*w*g,
            x*g+z*e+13*y*h+13*w*f,
            x*h+w*e+y*g+z*f)


def clear(vector,max_bits=2048,known_denominator=None):
    if len(vector) > MAX_STATES:
        raise Limit('Residual vector exceeds20000states')
    denominator = known_denominator or 1
    if known_denominator is None:
        for value in vector.values():
            assert len(value) == 4
            for q in value:
                assert max(abs(q.numerator).bit_length(),q.denominator.bit_length()) <= max_bits
                denominator = lcm(denominator,int(q.denominator))
    estimate = len(vector)*(384+4*((denominator.bit_length()+max_bits+7)//8))
    if estimate > 96*1024**2:
        raise Limit('Cleared integer record exceeds96MiB estimate')
    rows = tuple((state,tuple(int(q.numerator)*(denominator//int(q.denominator)) for q in value))
                 for state,value in vector.items() if value)
    return denominator,rows


class Residual:
    """Column names must refer to immutable vectors throughout this instance."""
    def __init__(self,field,get_column,boundary=lambda:None,max_bytes=64*1024**2):
        assert 0 < max_bytes <= 64*1024**2
        self.field,self.get_column,self.boundary = field,get_column,boundary
        self.max_bytes = max_bytes
        self.cache = OrderedDict()
        self.denominators = {}
        self.bytes = self.hits = self.misses = self.calls = 0
        self.max_den_bits = 0

    def column(self,name):
        if name in self.cache:
            self.hits += 1
            self.cache.move_to_end(name)
            return self.cache[name][0]
        self.misses += 1
        self.boundary()
        record = clear(self.get_column(name),known_denominator=self.denominators.get(name))
        denominator,rows = record
        self.denominators[name] = denominator
        cost = 1024+denominator.bit_length()//8
        for state,value in rows:
            cost += 384+sum(32+(abs(v).bit_length()+7)//8 for v in value)
        while self.cache and self.bytes+cost > self.max_bytes:
            _,(_,old_cost) = self.cache.popitem(last=False)
            self.bytes -= old_cost
        if cost <= self.max_bytes:
            self.cache[name] = record,cost
            self.bytes += cost
        return record

    def residual(self,target,columns,coefficients):
        assert len(columns) == len(coefficients) <= 300
        self.calls += 1
        target_den,target_rows = clear(target)
        denominator = target_den
        active = []
        for name,c in zip(columns,coefficients):
            if not c:
                continue
            coefficient_den,coefficient_row = clear({0:c},4096)
            integer_coefficient = coefficient_row[0][1]
            column_den = self.denominators.get(name)
            if column_den is None:
                column_den,_ = self.column(name)
            product_den = coefficient_den*column_den
            denominator = lcm(denominator,product_den)
            active.append((name,integer_coefficient,product_den))
        self.boundary()
        # At most20k states with four integer coordinates. Include the source
        # coefficient height in this preflight allocation estimate.
        limb_bound = denominator.bit_length()+6144+32
        if MAX_STATES*4*(32+(limb_bound+7)//8) > 512*1024**2:
            raise Limit('Residual accumulator exceeds512MiB allocation estimate')
        out = {s:tuple((denominator//target_den)*v for v in a) for s,a in target_rows}
        for name,coefficient,product_den in active:
            _,rows = self.column(name)
            scale = denominator//product_den
            for state,value in rows:
                product = multiply(coefficient,value)
                previous = out.get(state,(0,0,0,0))
                updated = tuple(a-scale*c for a,c in zip(previous,product))
                if any(updated):
                    out[state] = updated
                else:
                    out.pop(state,None)
            if len(out) > MAX_STATES:
                raise Limit('Residual accumulator exceeds20000states')
            self.boundary()
        self.max_den_bits = max(self.max_den_bits,denominator.bit_length())
        # Rational construction happens only for actual nonzero residuals.
        return {s:self.field(tuple(Fraction(a,denominator) for a in value)) for s,value in out.items()}

    def statistics(self):
        return {'calls':self.calls,'column_cache_hits':self.hits,'column_cache_misses':self.misses,
                'estimated_cache_bytes':self.bytes,'cache_cap':self.max_bytes,
                'largest_common_denominator_bits':self.max_den_bits}


def oracle(field,target,columns,coefficients,get_column):
    out = dict(target)
    for name,c in zip(columns,coefficients):
        if c:
            for state,v in get_column(name).items():
                value = out.get(state,field(0))-c*v
                if value:
                    out[state] = value
                else:
                    out.pop(state,None)
    return out


def controls(field):
    records = []
    for case in range(16):
        columns = {j:{s:field(tuple(f'{(case+2*j+3*s+k)%11-5}/{k+j+2}' for k in range(4)))
                      for s in range(5) if (s+j+case)%3} for j in range(4)}
        coefficients = [field(tuple(f'{case+j+2*k-7}/{k+j+3}' for k in range(4))) for j in range(4)]
        target = {}
        for j,c in enumerate(coefficients):
            for s,v in columns[j].items():
                target[s] = target.get(s,field(0))+c*v
        target = {s:v for s,v in target.items() if v}
        perturbation = field(('1/7','2/11','-3/13','5/17')) if case%2 else field(0)
        target[9] = perturbation
        if not perturbation:
            del target[9]
        engine = Residual(field,columns.__getitem__)
        got = engine.residual(target,list(columns),coefficients)
        expected = oracle(field,target,list(columns),coefficients,columns.__getitem__)
        assert got == expected == ({9:perturbation} if perturbation else {})
        # Repeat to cover cached denominator/integer-column reuse.
        assert engine.residual(target,list(columns),coefficients) == expected
        assert engine.hits > 0
        records.append({'case':case,'nonzero_residual':bool(got),'cache_hits':engine.hits})
    return records
