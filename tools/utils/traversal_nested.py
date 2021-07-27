#!/usr/bin/env python3 

import random
import inspect
import sys

# Counter of number of gennum's spawned
numgennum = 0

# Counter of number of candidates generated
numcand = 0

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
    global numgennum, method6_order
    numgennum += 1

    nums = list(range(maxnum+1))

    if randgennum:
        random.shuffle(nums)

    if method6_order == 'reverse':
        nums.reverse()

    for num in nums:
        yield num

# numcand: 40, numgennum: 12
#
# Has bug when len(coros) > 2
def method1():
    global numcand
    coros = [ Coro(gennum), Coro(gennum), Coro(gennum) ]
    cand = [ next(coros[i]) for i in range(0, len(coros)) ]
    
    yield cand
    numcand += 1
    
    for x in range(0, len(cand)):
        for xi in coros[x]:
            cand[x] = xi
            if x == 0:
                yield cand
                numcand += 1
            
            for y in range(0, x):
                if not coros[y]:
                    coros[y] = Coro(gennum)
                for yi in coros[y]:
                    cand[y] = yi
                    yield cand
                    numcand += 1

# numcand: 64, numgennum: 21
#
# method1, but handles arity > 2 correctly
def method2(coros, cand):
    global numcand
    yield tuple(cand)
    numcand += 1

    for x in range(len(coros)):
        for xi in coros[x]:
            cand[x] = xi
            newcoros = [Coro(gennum) for i in range(x)]
            for i in range(len(newcoros)):
                cand[i] = next(newcoros[i])
            for methcand in method2(newcoros, cand):
                yield methcand

def randorder(num):
    order = [ i for i in range(num) ]
    random.shuffle(order)
    return order

# Randomly pick the next coroutine on the queue to get a candidate from
method3_rndcoro = False

# numcand: 64, numgennum: 21
#
# method2, but with (possibly random) scheduling
def method3(coros, cand):
    global numcand
    yield tuple(cand)
    numcand += 1

    methcoros = []
    for x in range(len(coros)):
        for xi in coros[x]:
            cand[x] = xi
            newcoros = [ Coro(gennum) for i in range(x) ]
            for i in range(len(newcoros)):
                cand[i] = next(newcoros[i])
            methcoros.append(method3(newcoros, list(cand)))

    coroavail = True
    while coroavail:
        coroavail = False
        if method3_rndcoro:
            order = randorder(len(methcoros))
        else:
            order = range(len(methcoros))
        for x in order:
            try:
                yield tuple(next(methcoros[x]))
                coroavail = True
            except StopIteration:
                pass

# Either 'rnd', 'ltr', 'rtl'
method4_stuckmeth = 'ltr'
# Push recursive invocations to a queue, then stripe across them
# Probably doesn't need to be exposed? Always True is okay?
method4_coroqueue = True
# Either 'rnd', 'forward', 'reverse'
# Requires 'method5_coroqueue == True'
method4_corometh = 'forward'

# Note: 'rtl' + no queuing == 'ltr' + queuing + 'forward'
#       'ltr' + no queuing == 'rtl' + queuing + 'forward'

# numcand: 64, numgennum: 27
#
# method3, but more generic to allow random "stuck" positions
def method4(coros, cand, stuck=set()):
    #print("  "*len(inspect.stack(0)) + f'method4({coros}, {cand}, {stuck})')
    global numcand

    if len(stuck) == len(coros):
        yield tuple(cand)
        numcand += 1
    else:
        universe = set(range(len(coros)))
        free = universe.difference(stuck)
        if method4_stuckmeth == 'rnd':
            nextstuck = list(free)[random.randrange(0, len(free))]
        elif method4_stuckmeth == 'ltr':
            nextstuck = min(free)
        elif method4_stuckmeth == 'rtl':
            nextstuck = max(free)
        else:
            print(f'Unknown method4_stuckmeth: {method4_stuckmeth}')
            sys.exit(1)
        newstuck = stuck.union({nextstuck})
        methcoros = []
        while True:
            newcoros = [ Coro(gennum) if not x in newstuck else coros[x] for x in range(len(coros)) ]
            newcand = [ next(newcoros[x]) if not x in newstuck else cand[x] for x in range(len(cand)) ]
            if method4_coroqueue:
                methcoros.append(method4(newcoros, newcand, newstuck))
            else:
                for subcand in method4(newcoros, newcand, newstuck):
                    yield subcand
            try:
                cand[nextstuck] = next(coros[nextstuck])
            except StopIteration:
                break

        if method4_coroqueue:
            coroavail = True
            while coroavail:
                coroavail = False
                if method4_corometh == 'rnd':
                    order = randorder(len(methcoros))
                elif method4_corometh == 'forward':
                    order = range(len(methcoros))
                elif method4_corometh == 'reverse':
                    order = range(len(methcoros)-1, -1, -1)
                else:
                    print(f'Unknown method4_corometh: {method4_corometh}')
                    sys.exit(1)
                for x in order:
                    try:
                        yield tuple(next(methcoros[x]))
                        coroavail = True
                    except StopIteration:
                        pass

# numcand: 64, numgennum: 23 (wastes 2 of initial coros)
#
# method4, but we decide the next 'nextstuck' to avoid generating unused
#   coroutines.
def method4_1(coros, cand, stuck=set(), nextstuck=None):
    #print("  "*len(inspect.stack(0)) + f'method4_1({coros}, {cand}, {stuck})')
    global numcand

    if len(stuck) == len(coros):
        yield tuple(cand)
        numcand += 1
    else:
        universe = set(range(len(coros)))
        free = universe - stuck

        def getnewnextstuck(free):
            if method4_stuckmeth == 'rnd':
                return list(free)[random.randrange(0, len(free))]
            elif method4_stuckmeth == 'ltr':
                return min(free, default=-1)
            elif method4_stuckmeth == 'rtl':
                return max(free, default=-1)
            else:
                print(f'Unknown method4_stuckmeth: {method4_stuckmeth}')
                sys.exit(1)

        if nextstuck == None:
            nextstuck = getnewnextstuck(free)
        newstuck = stuck.union({nextstuck})

        nextnextstuck = getnewnextstuck(universe - newstuck)

        methcoros = []
        while True:
            newcoros = [ Coro(gennum) if x == nextnextstuck else coros[x] for x in range(len(coros)) ]
            newcand = [ next(newcoros[x]) if x == nextnextstuck else cand[x] for x in range(len(cand)) ]
            if method4_coroqueue:
                methcoros.append(method4_1(newcoros, newcand, newstuck, nextnextstuck))
            else:
                for subcand in method4_1(newcoros, newcand, newstuck, nextnextstuck):
                    yield subcand
            try:
                cand[nextstuck] = next(coros[nextstuck])
            except StopIteration:
                break

        if method4_coroqueue:
            coroavail = True
            while coroavail:
                coroavail = False
                if method4_corometh == 'rnd':
                    order = randorder(len(methcoros))
                elif method4_corometh == 'forward':
                    order = range(len(methcoros))
                elif method4_corometh == 'reverse':
                    order = range(len(methcoros)-1, -1, -1)
                else:
                    print(f'Unknown method4_corometh: {method4_corometh}')
                    sys.exit(1)
                for x in order:
                    try:
                        yield tuple(next(methcoros[x]))
                        coroavail = True
                    except StopIteration:
                        pass

# numcand: 64, numgennum: 21 (wastes all initial coros)
#
# method4, but with a different method of not wasting coroutines than 4_1
def method4_2(coros, cand, stuck=set()):
    #print("  "*len(inspect.stack(0)) + f'method4_2({coros}, {cand}, {stuck})')
    global numcand

    if len(stuck) == len(coros):
        yield tuple(cand)
        numcand += 1
    else:
        universe = set(range(len(coros)))
        free = universe.difference(stuck)

        if method4_stuckmeth == 'rnd':
            nextstuck = list(free)[random.randrange(0, len(free))]
        elif method4_stuckmeth == 'ltr':
            nextstuck = min(free)
        elif method4_stuckmeth == 'rtl':
            nextstuck = max(free)
        else:
            print(f'Unknown method4_stuckmeth: {method4_stuckmeth}')
            sys.exit(1)

        coros[nextstuck] = Coro(gennum)
        cand[nextstuck] = next(coros[nextstuck])

        newstuck = stuck.union({nextstuck})
        methcoros = []
        while True:
            methcoro = method4_2(list(coros), list(cand), newstuck)

            if method4_coroqueue:
                methcoros.append(methcoro)
            else:
                for subcand in methcoro:
                    yield subcand
            try:
                cand[nextstuck] = next(coros[nextstuck])
            except StopIteration:
                break

        if method4_coroqueue:
            coroavail = True
            while coroavail:
                coroavail = False
                if method4_corometh == 'rnd':
                    order = randorder(len(methcoros))
                elif method4_corometh == 'forward':
                    order = range(len(methcoros))
                elif method4_corometh == 'reverse':
                    order = range(len(methcoros)-1, -1, -1)
                else:
                    print(f'Unknown method4_corometh: {method4_corometh}')
                    sys.exit(1)
                for x in order:
                    try:
                        yield tuple(next(methcoros[x]))
                        coroavail = True
                    except StopIteration:
                        pass

# Whether to use a flat queue (False), or to make a separate queue for
#   each 'cand[i] = next(coros[i])' (True)
method5_nestedqueue = False

# numcand: 64, numgennum: 48
#
# Essentially a 'BFS' version of method2
# Note: Doesn't work with randgennum == True
def method5(coros, cand, stuck=set()):
    #print("  "*len(inspect.stack(0)) + f'method5({coros}, {cand}, {stuck})')
    global numcand

    yield tuple(cand)
    numcand += 1

    free = range(max(stuck, default=-1)+1, len(coros))

    methcoros = [[]]

    coroavail = True
    while coroavail:
        coroavail = False
        for i in free:
            try:
                cand[i] = next(coros[i])
                coroavail = True
                newstuck = stuck.union({i})
                newcoros = [ Coro(gennum) if not x in newstuck else coros[x] for x in range(len(coros)) ]
                newcand = [ next(newcoros[x]) if not x in newstuck else cand[x] for x in range(len(cand)) ]

                methcoros[-1].append(method5(newcoros, newcand, newstuck))
            except StopIteration:
                pass

        if method5_nestedqueue:
            methcoros.append([])

    for queue in methcoros:
        methcoroavail = True
        while methcoroavail:
            methcoroavail = False
            order = range(len(queue))
            for x in order:
                try:
                    yield tuple(next(queue[x]))
                    methcoroavail = True
                except StopIteration:
                    pass

# Either 'ltr' or 'rtl'
method5_1_stuckmeth = 'ltr'

method5_1_corometh = 'reverse'

# numcand: 64, numgennum: 21
#
# method5, but doesn't waste coroutines, and thus works with randgennum == True
def method5_1(coros, cand, stuck=set()):
    #print("  "*len(inspect.stack(0)) + f'method5_1({coros}, {cand}, {stuck})')
    global numcand

    yield tuple(cand)
    numcand += 1

    free = list(set(range(len(coros))) - stuck)

    if method5_1_stuckmeth == 'ltr':
        pass
    elif method5_1_stuckmeth == 'rtl':
        free.reverse()
    else:
        print(f'Unknown method5_1_stuckmeth: {method5_1_stuckmeth}')
        sys.exit(1)

    methcoros = [[]]

    coroavail = True
    while coroavail:
        coroavail = False
        for i in free:
            try:
                newcand = list(cand)
                newcand[i] = next(coros[i])
                coroavail = True
                newstuck = stuck.union(range(i+1))
                newcoros = [ Coro(gennum) if not x in newstuck else coros[x] for x in range(len(coros)) ]
                newcand = [ next(newcoros[x]) if not x in newstuck else newcand[x] for x in range(len(cand)) ]

                methcoros[-1].append(method5_1(newcoros, newcand, newstuck))
            except StopIteration:
                pass

        if method5_nestedqueue:
            methcoros.append([])

    for queue in methcoros:
        methcoroavail = True
        while methcoroavail:
            methcoroavail = False
            if method5_1_corometh == 'forward':
                order = range(len(queue))
            elif method5_1_corometh == 'reverse':
                order = range(len(queue)-1, -1, -1)
            else:
                print(f'Unknown method5_1_corometh: {method5_1_corometh}')
                sys.exit(1)
            for x in order:
                try:
                    yield tuple(next(queue[x]))
                    methcoroavail = True
                except StopIteration:
                    pass

method6_direction = 'ltr'
method6_order = 'forward'
# 'ordered' or 'striped'
method6_type = 'ordered'
# 'changed_first' or 'depth_first'
#method6_stripedprio = 'changed_first'
# 'sfs' (striped-first-search) or 'dfs' (depth-first-search)
#method6_stripedtype = 'sfs'
# 'sfs' (striped-first-search), 'bfs', or 'dfs'
# For type == 'striped': 'sfs' == method3,
#   'bfs' == (method5_nestedq == False), 'dfs' == (method5_nq == True)
# For type == 'ordered': 'sfs' == Error, 'bfs' == Error, 'dfs' == method4
method6_prio = 'sfs'

# Combination method for method3, 4_2, 5_1
def method6(coros, cand, stuck=set()):
    #print("  "*(len(inspect.stack(0))-2)+f'method6({coros}, {cand}, {stuck})')
    global numcand

    if method6_type == 'striped' or len(stuck) == len(coros):
        yield tuple(cand)
        numcand += 1

    if len(stuck) == len(cand):
        return

    methcoros = [[]]
    def finishmethcoros():
        for queue in methcoros:
            methcoroavail = True
            while methcoroavail:
                methcoroavail = False
                order = list(range(len(queue)))
                for x in order:
                    try:
                        yield tuple(next(queue[x]))
                        methcoroavail = True
                    except StopIteration:
                        pass


    if method6_type == 'striped':
        # method5_1
        free = list(range(max(stuck, default=-1)+1, len(cand)))
        if method6_direction == 'ltr':
            pass
        elif method6_direction == 'rtl':
            free.reverse()
        elif method6_direction == 'rnd':
            random.shuffle(free)
        else:
            print(f'Unknown method6_direction: {method6_direction}')
            sys.exit(1)

        def doinloop(i):
            try:
                newcand = list(cand)
                newcand[i] = next(coros[i])
                newstuck = stuck.union(range(i+1))
                newcoros = [ Coro(gennum) if not x in newstuck else None for x in range(len(coros)) ]
                newcand = [ next(newcoros[x]) if not x in newstuck else newcand[x] for x in range(len(cand)) ]

                methcoros[-1].append(method6(newcoros, newcand, newstuck))
                yield next(methcoros[-1][-1])
                #for exp in method6(newcoros, newcand, newstuck):
                #    yield exp
                yield True
            except StopIteration:
                yield False

        if method6_prio != 'dfs':
            coroavail = True
            while coroavail:
                coroavail = False
                for i in free:
                    for exp in doinloop(i):
                        if type(exp) is bool:
                            coroavail |= exp
                        else:
                            yield exp
                    #coroavail |= doinloop(i)
                if method6_prio == 'sfs':
                    pass
                elif method6_prio == 'bfs':
                    for exp in finishmethcoros():
                        yield exp
                else:
                    print(f'Invalid method6_prio: {method6_prio}')
                    sys.exit(1)
        else:
            for i in free:
                coroavail = True
                while coroavail:
                    #coroavail = doinloop(i)
                    for exp in doinloop(i):
                        if type(exp) is bool:
                            coroavail = exp
                        else:
                            yield exp
    elif method6_type == 'ordered':
        # method 4_2
        universe = set(range(len(cand)))
        free = universe.difference(stuck)

        if method6_direction == 'rnd':
            nextstuck = list(free)[random.randrange(0, len(free))]
        elif method6_direction == 'ltr':
            nextstuck = max(free)
        elif method6_direction == 'rtl':
            nextstuck = min(free)
        else:
            print(f'Unknown method6_direction: {method6_direction}')
            sys.exit(1)

        #coros[nextstuck] = Coro(gennum)
        #cand[nextstuck] = next(coros[nextstuck])
        newcoro = Coro(gennum)
        newstuck = stuck.union({nextstuck})

        for exp in newcoro:
            cand[nextstuck] = exp
            #methcoros[-1].append(method6([ None for x in range(len(coros)) ], list(cand), newstuck))
            for exp in method6([None]*len(coros), list(cand), newstuck):
                yield exp
    else:
        print(f'Unknown method6_type: {method6_type}')
        sys.exit(1)

    for exp in finishmethcoros():
        yield exp

# Completely random, i.e. same as '--gen_method rnd'
def randmethod(candsize):
    global numcand
    generatedset = set()

    while len(generatedset) != (maxnum+1)**candsize:
        cand = tuple(random.randrange(0, maxnum+1) for x in range(candsize))
        if not cand in generatedset:
            generatedset.add(cand)
            yield cand
            numcand += 1

glcoros = [ Coro(gennum) for x in range(candsize) ]
glcand = [ next(coro) for coro in glcoros ]

correctcands = set()

for cand in method2(glcoros, glcand):
    correctcands.add(cand)

#method2(glcoros, glcand)

numiterations = 1
prettyprint = True

numcand = 0
numgennum = 0
for x in range(numiterations):
    # For method4_2; doesn't matter what's here, just that it has right length
    #glcoros = [ None, None, None ]
    #glcand = [ 0, 0, 0 ]

    for mtype in ('ordered', 'striped'):
        for prio in ('sfs', 'bfs', 'dfs'):
            for direction in ('ltr', 'rtl'):
                for order in ('forward', 'reverse'):
                    if mtype == 'ordered' and prio != 'sfs':
                        continue
                    if mtype == 'striped' and prio == 'dfs' and direction == 'rnd':
                        continue
                    method6_direction = direction
                    method6_order = order
                    method6_type = mtype
                    method6_prio = prio
                    if mtype == 'ordered':
                        method6_prio = 'ignored'
                        glcoros = [ None for x in range(candsize) ]
                        glcand = [ None for x in range(candsize) ]
                    else:
                        glcoros = [ Coro(gennum) for x in range(candsize) ]
                        glcand = [ next(coro) for coro in glcoros ]
                    newcands = set()

                    print(f'direction: {direction}, order: {order}, type: {mtype}, prio: {method6_prio}')
                    
                    for cand in method6(glcoros, glcand):
                        newcands.add(cand)
                        if prettyprint:
                            print(cand)
                        else:
                            print(f'{cand[0]}{cand[1]}{cand[2]}', end='')

                    if correctcands != newcands:
                        print()
                        print("New method didn't produce correct candidates:")
                        for cand in correctcands.difference(newcands):
                            print(f"New is missing: {cand}")

if prettyprint:
    print()

    print(f'Number of candidates generated: {numcand}')
    print(f'Number of coroutines created: {numgennum}')
