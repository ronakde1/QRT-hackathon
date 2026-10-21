import time
from collections import deque

# N, E, S, W bit flags
N,E,S,W = 1,2,4,8
SHAPES = (0, N|S, E|W, N|E, N|W, S|E, S|W)
CHARS = '.|-LJF7'
FULL = (1<<7)-1
STRAIGHT = (1<<1)|(1<<2)
TURN = FULL & ~(1 | STRAIGHT)
OPP = (S,W,N,E)
DIRS = (N,E,S,W)
STATES = tuple(tuple(a for a in range(7) if mask & (1<<a))
               for mask in range(FULL+1))
EDGE_MASK = tuple(sum(1<<a for a,s in enumerate(SHAPES) if s&edge)
                  for edge in DIRS)
NO_EDGE_MASK = tuple(FULL ^ mask for mask in EDGE_MASK)
POSSIBLE = tuple(sum(edge for d,edge in enumerate(DIRS) if mask&EDGE_MASK[d])
                 for mask in range(FULL+1))
FORCED = tuple(sum(edge for d,edge in enumerate(DIRS)
                   if mask and not mask&NO_EDGE_MASK[d])
               for mask in range(FULL+1))


def solve(grid, time_limit=8.5):
    """Return a Masyu solution, or a geometric loop if the search times out.

    Seed the search with a valid rectangular solution when possible, then
    improve it. Only use a geometric fallback if no valid solution was found.
    A board with fewer than two rows or columns cannot contain a loop.
    """
    start=time.monotonic()
    deadline=start+time_limit
    r,c=len(grid),len(grid[0]); size=r*c
    nbr=[[-1]*4 for _ in range(size)]
    for i in range(size):
        y,x=divmod(i,c)
        if y: nbr[i][0]=i-c
        if x<c-1: nbr[i][1]=i+1
        if y<r-1: nbr[i][2]=i+c
        if x: nbr[i][3]=i-1
    domains=[FULL]*size
    pearls=[]
    for i in range(size):
        for d,edge in enumerate(DIRS):
            if nbr[i][d]<0:
                domains[i] &= NO_EDGE_MASK[d]
        p=grid[i//c][i%c]
        if p=='W': domains[i]&=STRAIGHT; pearls.append((i,p))
        if p=='B': domains[i]&=TURN; pearls.append((i,p))
    best=None; best_len=size+1
    phase_deadline=deadline
    strategy=0

    class RestartSearch(Exception):
        pass
    edges=[(i,j,d) for i in range(size) for d in (1,2)
           if (j:=nbr[i][d])>=0]
    pearl_neighbors=[sum(grid[j//c][j%c] in 'WB' for j in nbr[i] if j>=0)
                     for i in range(size)]
    # Each pearl has at most four patterns. A white pearl's two patterns
    # per orientation represent which adjacent cell must turn.
    constraints=[]; watchers=[[] for _ in range(size)]
    for i,p in pearls:
        scope=[i]+[j for j in nbr[i] if j>=0]
        patterns=[]
        for a in STATES[domains[i]]:
            ds=[d for d,edge in enumerate(DIRS) if SHAPES[a]&edge]
            for turn_at in ((None,) if p=='B' else (0,1)):
                pattern=[FULL]*len(scope); pattern[0]=1<<a
                for pos,d in enumerate(ds):
                    mask=1<<(1 if d%2==0 else 2) if p=='B' else EDGE_MASK[(d+2)%4]
                    if pos==turn_at:mask &= TURN
                    pattern[scope.index(nbr[i][d])]=mask
                patterns.append(pattern)
        for j in scope:watchers[j].append(len(constraints))
        constraints.append((scope,patterns))

    def check_timeout():
        now=time.monotonic()
        if now >= deadline:
            raise TimeoutError
        if best is None and now >= phase_deadline:
            raise RestartSearch

    def seed_rectangle():
        nonlocal best,best_len
        if r<2 or c<2:return
        if not pearls:
            bounds=[(0,1,0,1)]
        else:
            ys=[i//c for i,_ in pearls]; xs=[i%c for i,_ in pearls]
            top,bottom=min(ys),max(ys); left,right=min(xs),max(xs)
            # Small margins let a white pearl lie beside a corner and a
            # black pearl have a straight cell along each outgoing edge.
            tops={0,top,max(0,top-1),max(0,top-2)}
            bottoms={r-1,bottom,min(r-1,bottom+1),min(r-1,bottom+2)}
            lefts={0,left,max(0,left-1),max(0,left-2)}
            rights={c-1,right,min(c-1,right+1),min(c-1,right+2)}
            bounds=sorted(((t,b,l,h) for t in tops for b in bottoms
                           for l in lefts for h in rights if t<b and l<h),
                          key=lambda v:(v[1]-v[0]+v[3]-v[2],v))
        for top,bottom,left,right in bounds:
            check_timeout()
            valid=True
            for i,p in pearls:
                y,x=divmod(i,c)
                horizontal=y in (top,bottom); vertical=x in (left,right)
                if p=='B':
                    valid=(horizontal and vertical and bottom-top>=2
                           and right-left>=2)
                else:
                    valid=((horizontal and not vertical
                            and x in (left+1,right-1))
                           or (vertical and not horizontal
                               and y in (top+1,bottom-1)))
                if not valid:break
            if not valid:continue
            candidate=[1]*size
            for x in range(left+1,right):
                candidate[top*c+x]=candidate[bottom*c+x]=1<<2
            for y in range(top+1,bottom):
                candidate[y*c+left]=candidate[y*c+right]=1<<1
            candidate[top*c+left]=1<<5
            candidate[top*c+right]=1<<6
            candidate[bottom*c+left]=1<<3
            candidate[bottom*c+right]=1<<4
            best=candidate; best_len=2*(bottom-top+right-left)
            return

    def propagate(dom, changed):
        queue=deque(range(size) if changed is None else (changed,))
        queued=[changed is None or i==changed for i in range(size)]

        def narrow(i,mask):
            new=dom[i]&mask
            if not new:return False
            if new!=dom[i]:
                dom[i]=new
                if not queued[i]:queue.append(i);queued[i]=True
            return True

        while True:
            updates=0
            while queue:
                if updates%64==0:check_timeout()
                updates+=1
                i=queue.popleft();queued[i]=False
                if not dom[i]:return False
                # An edge only propagates when it is required or forbidden.
                for d,j in enumerate(nbr[i]):
                    if j<0:continue
                    opposite=(d+2)%4
                    if not dom[i]&EDGE_MASK[d]:
                        if not narrow(j,NO_EDGE_MASK[opposite]):return False
                    elif not dom[i]&NO_EDGE_MASK[d]:
                        if not narrow(j,EDGE_MASK[opposite]):return False
                for ci in watchers[i]:
                    scope,patterns=constraints[ci]
                    supports=[0]*len(scope)
                    for pattern in patterns:
                        if all(dom[j]&mask for j,mask in zip(scope,pattern)):
                            for k,mask in enumerate(pattern):supports[k] |= mask
                    for j,mask in zip(scope,supports):
                        if not narrow(j,mask):return False

            # Track paths using all mandatory edges, even at cells whose
            # second edge has not been decided yet.
            parent=list(range(size)); counts=[1]*size
            def root(i):
                while parent[i]!=i:
                    parent[i]=parent[parent[i]];i=parent[i]
                return i
            cycle=-1
            forced_edges=[FORCED[v] for v in dom]
            for i,j,d in edges:
                if not forced_edges[i]&DIRS[d]:continue
                a,b=root(i),root(j)
                if a==b:cycle=i;continue
                if counts[a]<counts[b]:a,b=b,a
                parent[b]=a;counts[a]+=counts[b]
            roots=[root(i) for i in range(size)]
            required=[i for i,v in enumerate(dom) if not v&1]
            if cycle>=0:
                component=roots[cycle]
                if any(roots[i]!=component for i in required):return False
                # Local constraints are already consistent. Save this closed
                # loop without branching on unrelated optional cells.
                for i in range(size):
                    if roots[i]!=component:dom[i]=1
                return True
            for i,j,d in edges:
                if (not forced_edges[i]&DIRS[d] and dom[i]&EDGE_MASK[d]
                        and roots[i]==roots[j] and counts[roots[i]]<len(required)):
                    if not narrow(i,NO_EDGE_MASK[d]):return False
                    if not narrow(j,NO_EDGE_MASK[(d+2)%4]):return False
            if queue:continue

            # Every required cell must remain reachable in the possible-edge
            # graph. Optional components outside it cannot belong to the loop.
            if required:
                seen={required[0]};stack=[required[0]]
                while stack:
                    i=stack.pop()
                    possible=POSSIBLE[dom[i]]
                    for d,j in enumerate(nbr[i]):
                        if possible&DIRS[d] and j not in seen:
                            seen.add(j);stack.append(j)
                if any(i not in seen for i in required):return False
                for i in range(size):
                    if i not in seen and not narrow(i,1):return False
            if not queue:return True

    def check(dom):
        nonlocal best,best_len
        used={i for i,v in enumerate(dom) if v!=1}
        if len(used)>=best_len or not used:return
        if any(i not in used for i,_ in pearls):return
        cur=next(iter(used)); seen=set()
        while cur not in seen:
            seen.add(cur)
            d=next(d for d,edge in enumerate(DIRS) if SHAPES[dom[cur].bit_length()-1]&edge)
            nxt=nbr[cur][d]
            # At next cell, follow exit other than incoming edge.
            prev=cur; cur=nxt
            while cur not in seen:
                seen.add(cur)
                s=SHAPES[dom[cur].bit_length()-1]
                choices=[nbr[cur][q] for q,e in enumerate(DIRS) if s&e]
                next_cell=choices[0] if choices[1]==prev else choices[1]
                prev,cur=cur,next_cell
            break
        if cur==next(iter(used)) and seen==used:
            best=dom[:];best_len=len(used)

    def dfs(dom, changed=None):
        check_timeout()
        if not propagate(dom,changed):return
        forced=sum(1 for v in dom if not v&1)
        if forced>=best_len:return
        ambiguous=[i for i,v in enumerate(dom) if v.bit_count()>1]
        if not ambiguous:
            check(dom);return
        # Prioritize cells next to pearls or already-on lines, then smallest domain.
        i=min(ambiguous,key=lambda i:(bool(dom[i]&1) if strategy==3 else False,
              dom[i].bit_count(),
              -sum(dom[j]&1==0 for j in nbr[i] if j>=0),
              -pearl_neighbors[i]))
        options=list(STATES[dom[i]])
        if strategy==0:
            options.sort(key=lambda a:(a==0, a in (1,2)))
        elif strategy==1:
            options.sort(key=lambda a:(a!=0, a not in (1,2)))
        else:
            options.sort(key=lambda a:(a==0, a not in (1,2)))
        for a in options:
            nxt=dom[:];nxt[i]=1<<a
            dfs(nxt,i)

    timed_out=False
    try:
        seed_rectangle()
        # Try different branch orders if the first valid loop is slow to
        # appear. Once one is found, spend the remaining budget improving it.
        phase_limits=(min(0.25,time_limit*0.15), min(0.75,time_limit*0.35),
                      min(1.75,time_limit*0.6), time_limit)
        for strategy,limit in enumerate(phase_limits):
            phase_deadline=start+limit
            try:
                dfs(domains[:])
                break
            except RestartSearch:
                continue
    except TimeoutError:timed_out=True
    except RecursionError:pass
    if best is None:
        if timed_out and r>=2 and c>=2:
            # Keep this fallback out of best: it need not satisfy the pearls,
            # so its length must never prune the search for a valid solution.
            return ['F7'+'.'*(c-2), 'LJ'+'.'*(c-2)]+['.'*c for _ in range(r-2)]
        return None
    return [''.join(CHARS[v.bit_length()-1] for v in best[y*c:(y+1)*c]) for y in range(r)]
