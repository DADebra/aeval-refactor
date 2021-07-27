#!/usr/bin/env python3 

import random
import inspect
import sys
from itertools import combinations

# Counter of number of gennum's spawned
numgennum = 0

# Counter of number of candidates generated
totalnumcand = 0
numcand = { 0: 0, 1: 0, 2: 0, 3: 0 }

# Number of numbers per candidate
candsize = 3

# Wrapper around generator function:
# Python generator functions/objects have no way to determine when they're done
class Coro:
    def __init__(self, fncoro):
        self.done = False
        self.fncoro = fncoro
        self.coro = self.coro_fn()

    def __del__(self):
        if not self.done:
            print(f"Coroutine {self} was only partially done!")
        
    def __bool__(self):
        return not self.done
    
    def __iter__(self):
        return self.coro
    
    def __next__(self):
        return next(self.coro)

    def __repr__(self):
        return "{}".format(hex(id(self)))

    def coro_fn(self):
        for val in self.fncoro():
            yield val
        self.done = True

maxnum = 3

randgennum = False
def gennum():
    #print("Starting new gennum!")
    global numgennum
    numgennum += 1

    nums = list(range(maxnum+1))

    if randgennum:
        random.shuffle(nums)

    for num in nums:
        if num == 3:
            pass
            #breakpoint()
        yield num

# numcand: 64, numgennum: 21
#
# method1, but handles arity > 2 correctly
def method2(coros, cand):
    global numcand, totalnumcand
    yield tuple(cand)
    totalnumcand += 1
    for c in set(cand):
        numcand[c] += 1

    for x in range(len(coros)):
        for xi in coros[x]:
            cand[x] = xi
            newcoros = [Coro(gennum) for i in range(x)]
            for i in range(len(newcoros)):
                cand[i] = next(newcoros[i])
            for methcand in method2(newcoros, cand):
                yield methcand

# 3: 0.1 means that at most 1/10 of candidates genned are 3, with catch up
priomap = { 0: 1, 1: 1, 2: 1, 3: 0.1 }
defpaths = { key: [] for key in priomap.keys() }

def shoulddeferint(i):
    global totalnumcand, priomap, numcand
    if numcand[i] == 0:
        return False
    return numcand[i] > int(priomap[i]*totalnumcand)

    #mod = int(1/priomap[i])
    #if mod == 0:
    #    return False
    #expr = totalnumcand % mod
    ##print(f"i: {i}, numcand[i]: {numcand[i]}, numcand[i] % {mod}: {expr}")
    #return expr != 0

def shoulddefercand(cand):
    global numcand, totalnumcand, priomap, defpaths
    
    for c in set(cand):
        if shoulddeferint(c):
            return True

    return False

def method2_prio_rec(coros, cand):
    global numcand, totalnumcand, priomap, defpaths
    yield tuple(cand)
    totalnumcand += 1
    for c in set(cand):
        numcand[c] += 1

    for x in range(len(coros)):
        for xi in coros[x]:
            cand[x] = xi
            newcoros = [Coro(gennum) for i in range(x)]
            for i in range(len(newcoros)):
                cand[i] = next(newcoros[i])
            if shoulddefercand(cand):
                print(f"Deferring cand: {cand}")
                defpaths[xi].append(method2_prio_rec(newcoros, list(cand)))
            else:
                for methcand in method2_prio_rec(newcoros, list(cand)):
                    yield methcand

def method2_prio(coros, cand):
    for methcand in method2_prio_rec(coros, cand):
        yield methcand

    for i, methqueue in defpaths.items():
        for meth in methqueue:
            for methcand in meth:
                yield methcand

def method4_2(coros, cand, stuck=set()):
    #print("  "*len(inspect.stack(0)) + f'method4_2({coros}, {cand}, {stuck})')
    global totalnumcand, numcand

    if len(stuck) == len(coros):
        yield tuple(cand)
        return

    universe = set(range(len(coros)))
    free = universe.difference(stuck)

    nextstuck = min(free)

    coros[nextstuck] = Coro(gennum)
    cand[nextstuck] = next(coros[nextstuck])

    newstuck = stuck.union({nextstuck})
    methcoros = []
    while True:
        methcoro = method4_2(list(coros), list(cand), newstuck)

        methcoros.append(methcoro)
        try:
            cand[nextstuck] = next(coros[nextstuck])
        except StopIteration:
            break

    coroavail = True
    while coroavail:
        coroavail = False
        order = list(range(len(methcoros)))
        #order.reverse()
        for x in order:
            try:
                yield tuple(next(methcoros[x]))
                coroavail = True
            except StopIteration:
                pass

def method_prio(method, coros, cand):
    global priomap, totalnumcand, numcand
    numiter = 0
    defcands = dict()
    for clen in range(1, maxnum+1):
        for c in combinations(range(maxnum+1), clen):
            defcands[tuple(c)] = []

    meth = method(coros, cand)
    done = False

    while not done:
        retexp = None

        def getMinDefCand(checkprio, travdone = False):
            # (key, numiter, exp)
            minexp = (None, -1, None)
            for k, cands in defcands.items():
                if not (checkprio and shoulddefercand(k)) and len(cands) != 0:
                    if minexp[0] == None or cands[0][0] < minexp[1]:
                        minexp = (k, cands[0][0], cands[0][1])

            if minexp[0] == None and checkprio and travdone:
                # All deferred candidates are unusable
                # (key, numiter, exp, compoundpriority)
                minexp = (None, -1, None, -1)
                for k in defcands.keys():
                    #prod = 1
                    #for v in k:
                    #    prod *= priomap[v]
                    ksum = sum([ priomap[v] for v in k ])
                    if len(defcands[k]) != 0 and (minexp[0] == None or
                    ksum > minexp[3] or (ksum == minexp[3] and
                    defcands[k][0][0] < minexp[1])):
                        minexp = (k, defcands[k][0][0], defcands[k][0][1], ksum)

            if minexp[0] != None:
                print(f"Using deferred candidate {minexp[2]}")
                defcands[minexp[0]].pop(0)
                return minexp[2]
            return None

        retexp = getMinDefCand(True)

        #for c, cands in defcands.items():
        #    if not shoulddefercand(c) and len(cands) != 0:
        #        retexp = cands[0]
        #        defcands[c].pop(0)
        #        print(f"Using deferred candidate {retexp}")
        #        break

        #if retexp == None:
        #    maxprio = max(priomap)
        #    maxprios = set()
        #    for k, v in priomap.items():
        #        if v == maxprio:
        #            maxprios.add(k)
        #    minprio = [ (k, min(vals)) for vals in defcands

            
        
        if retexp == None:
            try:
                exp = next(meth)
                numiter += 1
                if not shoulddefercand(exp):
                    retexp = exp
                else:
                    print(f"Deferring cand: {exp}")
                    defcands[tuple(sorted(set(exp)))].append((numiter, exp))
            except StopIteration:
                retexp = getMinDefCand(True, True)
                if retexp == None:
                    retexp = getMinDefCand(False, True)
                if retexp == None:
                    done = True

        if retexp != None:
            totalnumcand += 1
            for c in set(retexp):
                numcand[c] += 1
            yield retexp


    #for exp in method4_prio_rec(coros, cand):
    #    retexp = None
    #    if shoulddefercand(exp):
    #        print(f"Deferring cand: {exp}")
    #        defcands[tuple(sorted(set(exp)))].append(exp)

    #        for c, cands in defcands.items():
    #            if not shoulddefercand(c) and len(cands) != 0:
    #                retexp = cands[0]
    #                #print(f"Using deferred candidate {retexp}")
    #                defcands[c].pop(0)
    #    else:
    #        retexp = exp

    #    if retexp != None:
    #        totalnumcand += 1
    #        for c in set(retexp):
    #            numcand[c] += 1
    #        yield retexp

    #for k, cands in defcands.items():
    #    for exp in cands:
    #        #print(f"(end) Using deferred candidate {exp}")
    #        totalnumcand += 1
    #        for c in set(exp):
    #            numcand[c] += 1
    #        yield exp


glcoros = [ gennum(), gennum(), gennum() ]
glcand = [ next(coro) for coro in glcoros ]

correctcands = set()

for cand in method2(glcoros, glcand):
    correctcands.add(cand)

numcand = { 0: 0, 1: 0, 2: 0, 3: 0 }
totalnumcand = 0
numgennum = 0

newcands = set()
glcoros = [ Coro(gennum) for x in range(3) ]
glcand = [ next(coro) for coro in glcoros ]
#glcoros = [ None, None, None ]
#glcand = [ 0, 0, 0 ]

for cand in method_prio(method4_2, glcoros, glcand):
    newcands.add(cand)
    print(cand)

if correctcands != newcands:
    print()
    print("New method didn't produce correct candidates:")
    for cand in correctcands.difference(newcands):
        print(f"New is missing: {cand}")

print()

print(f'Number of candidates generated for each number: {numcand}')
print(f'Total number of candidates generated: {totalnumcand}')
print(f'Number of coroutines created: {numgennum}')
