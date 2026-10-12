"""Bounded exact whole-left-field actions; no numerical approximation.

Only explicitly registered fields use this cache. Registration keys include
the complete immutable field contents, so separately reconstructed equal
fields can reuse actions. The original mode oracle remains available.
"""
from collections import OrderedDict


class ExactModeCache:
    def __init__(self,module,field,*,max_bytes=192*1024**2,max_entries=30000):
        assert isinstance(module.ONE,field)
        assert 0 < max_bytes <= 192*1024**2 and 0 < max_entries <= 30000
        self.module,self.field = module,field
        self.original_mode = module.mode
        self.max_bytes,self.max_entries = max_bytes,max_entries
        self.snapshots,self.tokens = [],{}
        self.cache = OrderedDict()
        self.bytes = self.peak_bytes = self.hits = self.misses = self.calls = 0

    @staticmethod
    def key(left):
        return tuple(sorted((state,tuple(c)) for state,c in left.items()))

    def register(self,left):
        assert len(left) <= 500 and all(isinstance(c,self.field) for c in left.values())
        key = self.key(left)
        if key not in self.tokens:
            assert len(self.tokens) < 32
            self.tokens[key] = len(self.snapshots)
            self.snapshots.append(dict(left))
        return self.tokens[key]

    def action(self,token,n,state):
        key = (token,n,state)
        if key in self.cache:
            self.hits += 1
            self.cache.move_to_end(key)
            return self.cache[key][0]
        self.misses += 1
        vector = self.original_mode(self.snapshots[token],n,{state:self.module.ONE})
        assert len(vector) <= 20000
        row = tuple(vector.items())
        cost = 1024
        for target,c in row:
            bits = max(max(abs(q.numerator).bit_length(),q.denominator.bit_length()) for q in c)
            assert bits <= 2048
            # Include state tuples/integers, four GMP rationals, dict/LRU keys,
            # and conservative numerator/denominator limb storage.
            cost += 1024+8*((bits+7)//8)+40*len(target[1])
        if cost <= self.max_bytes:
            while self.cache and (self.bytes+cost > self.max_bytes or len(self.cache) >= self.max_entries):
                _,(_,old_cost) = self.cache.popitem(last=False)
                self.bytes -= old_cost
            self.cache[key] = row,cost
            self.bytes += cost
            self.peak_bytes = max(self.peak_bytes,self.bytes)
        return row

    def mode(self,left,n,right):
        token = self.tokens.get(self.key(left)) if len(left) <= 500 else None
        if token is None:
            return self.original_mode(left,n,right)
        self.calls += 1
        out = {}
        zero = self.module.ZERO_A
        for state,c in right.items():
            if not c:
                continue
            for target,value in self.action(token,n,state):
                new = out.get(target,zero)+c*value
                if new:
                    out[target] = new
                else:
                    out.pop(target,None)
        return out

    def statistics(self):
        return {'arithmetic':'exact Q(sqrt13,sqrtminus3)',
                'whole_mode_calls':self.calls,'basis_hits':self.hits,
                'basis_misses':self.misses,'estimated_bytes':self.bytes,
                'peak_estimated_bytes':self.peak_bytes,'byte_cap':self.max_bytes,
                'entries':len(self.cache),'entry_cap':self.max_entries,
                'registered_fields':len(self.snapshots)}
