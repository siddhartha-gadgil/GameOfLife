import json, os, sys
HERE=os.path.dirname(os.path.abspath(__file__))
for d in ('life_machine','life_gates'): sys.path.insert(0, os.path.join(HERE,'..',d))
from net import piece_cells, env_box
from life import cells_of_window, bbox, glider_at
SE,NE=(1,1),(1,-1)
spec=json.load(open(os.path.join(HERE,'results','cat_specs.json')))
def far(b1,b2): return b1[2]+2<b2[0] or b2[2]+2<b1[0] or b1[3]+2<b2[1] or b2[3]+2<b1[1]
def sh(b,dx,dy): return (b[0]+dx,b[1]+dy,b[2]+dx,b[3]+dy)
for name,v,dirn in (('pass_NZ',(72,72),SE),('pass_Z',(72,-72),NE)):
    e=[x for x in spec['catalogue'] if x['name']==name][0]
    boxes=[env_box(tuple(p)) for p in e['pieces']]
    ec=cells_of_window(e['eater_cells']['x0'],e['eater_cells']['y0'],e['eater_cells']['rows'])
    boxes.append(bbox(ec))
    print(name,'boxes',boxes)
    print(' pairwise far:',[[far(a,b) for b in boxes] for a in boxes])
    for j in (1,2,3):
        print(' j',j,'copy far:',all(far(a,sh(b,v[0]*j,v[1]*j)) for a in boxes for b in boxes))
    wl=e['In'][0]['wl']; t0=int(e['t0'])
    path=[]
    for k in range(4):
        cs=set()
        for t in range(t0+72*k, t0+72*k+73): cs|=glider_at(dirn, wl[1], wl[2], t)
        path.append(bbox(cs))
    print(' path',path)
    print(' path vs own boxes far:',[[far(p,b) for b in boxes] for p in path])
    for j in (1,2,3):
        print(' j',j,'path vs copies:',all(far(p,sh(b,v[0]*j,v[1]*j)) for p in path for b in boxes),
              'copies path vs own:', all(far(b,sh(p,v[0]*j,v[1]*j)) for p in path for b in boxes))
