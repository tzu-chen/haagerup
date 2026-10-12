"""Bounded whole-left-field mode cache, finite-prime arithmetic ONLY.

Registered left dictionaries must remain immutable. Strong references prevent
identity reuse; independent snapshots are used by the uncached mode oracle.
The helper never changes the mode engine or field implementation itself.
"""
from collections import OrderedDict


class CacheLimit(Exception):
    pass


class PrimeModeCache:
    def __init__(self,module,prime,*,max_terms=300000,max_entries=50000,
                 max_left_fields=256,max_action_terms=50000):
        assert isinstance(module.ONE,int) and int(module.ONE) == 1
        assert not isinstance(module.ONE,tuple),'Refusing characteristic-zero field arithmetic'
        assert 0 < max_terms <= 300000 and 0 < max_entries <= 50000
        self.module,self.prime = module,prime
        self.original_mode = module.mode
        self.max_terms,self.max_entries = max_terms,max_entries
        self.max_left_fields,self.max_action_terms = max_left_fields,max_action_terms
        self.left_refs,self.left_snapshots,self.left_tokens = {},{},{}
        self.cache = OrderedDict()
        self.terms = self.peak_terms = self.peak_entries = 0
        self.hits = self.misses = self.evictions = self.calls = 0

    def register(self,left):
        key = id(left)
        if key in self.left_refs:
            assert self.left_refs[key] is left
            return self.left_tokens[key]
        if len(self.left_refs) >= self.max_left_fields:
            raise CacheLimit('Registered-left-field cap; fields must be reused rather than recreated')
        assert all(isinstance(c,int) for c in left.values())
        token = len(self.left_refs)
        self.left_refs[key] = left  # Keep the original alive: ids cannot be reused.
        self.left_snapshots[token] = dict(left)  # Immutable-by-contract oracle input.
        self.left_tokens[key] = token
        return token

    def action(self,token,n,state):
        key = (token,n,state)
        if key in self.cache:
            self.hits += 1
            self.cache.move_to_end(key)
            return self.cache[key]
        self.misses += 1
        vector = self.original_mode(self.left_snapshots[token],n,{state:self.module.ONE})
        if len(vector) > self.max_action_terms:
            raise CacheLimit('Single composite basis action exceeded its reviewed term cap')
        row = tuple((s,int(c) % self.prime) for s,c in vector.items() if c)
        if len(row) <= self.max_terms:
            while self.cache and (self.terms+len(row) > self.max_terms or len(self.cache) >= self.max_entries):
                _,old = self.cache.popitem(last=False)
                self.terms -= len(old)
                self.evictions += 1
            self.cache[key] = row
            self.terms += len(row)
            self.peak_terms = max(self.peak_terms,self.terms)
            self.peak_entries = max(self.peak_entries,len(self.cache))
        return row

    def mode(self,left,n,right):
        token = self.register(left)
        self.calls += 1
        out = {}
        prime = self.prime
        for state,coefficient in right.items():
            coefficient = int(coefficient) % prime
            if not coefficient:
                continue
            for target,value in self.action(token,n,state):
                new = (out.get(target,0)+coefficient*value) % prime
                if new:
                    out[target] = new
                else:
                    out.pop(target,None)
        return out

    def clear(self):
        self.cache.clear()
        self.terms = 0

    def statistics(self):
        return {'whole_mode_calls':self.calls,'basis_cache_hits':self.hits,
                'basis_cache_misses':self.misses,'basis_cache_evictions':self.evictions,
                'retained_terms':self.terms,'retained_entries':len(self.cache),
                'peak_terms':self.peak_terms,'peak_entries':self.peak_entries,
                'registered_left_fields':len(self.left_refs),
                'term_cap':self.max_terms,'entry_cap':self.max_entries,
                'arithmetic':'Plain integer modular accumulation of cached composite basis actions'}
