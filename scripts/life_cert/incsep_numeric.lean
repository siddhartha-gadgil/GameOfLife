import LeanTheory.Theory.Life.MainTheorem
open Lean Meta LeanTheory.Computability LeanTheory.Life LeanTheory.Life.LP

/- Numerical sanity check (untrusted, not part of the library) of the far fields of `IncSep`
(side windows + RF_J corner window) for the test programs. Run: `lake env lean
scripts/life_cert/incsep_numeric.lean` (edit the program list at the end). Register strips are
omitted (covered by the proved lane fields); the increment run is over-approximated by the run
regions of `incRunBox`. -/

def allBases : List Base :=
  [.orGate, .eatNZ, .eatZ] ++ (List.range 8).map .rf ++ (List.range 8).map .bodyDec ++
  (List.range 3).map .bodyInc ++ (List.range 28).map .dz2g ++ (List.range 3).map .stNZ ++
  (List.range 3).map .stZ

def baseExpr : Base → Expr
  | .orGate => mkConst ``Base.orGate
  | .eatNZ => mkConst ``Base.eatNZ
  | .eatZ => mkConst ``Base.eatZ
  | .rf k => mkApp (mkConst ``Base.rf) (mkNatLit k)
  | .bodyDec k => mkApp (mkConst ``Base.bodyDec) (mkNatLit k)
  | .bodyInc k => mkApp (mkConst ``Base.bodyInc) (mkNatLit k)
  | .dz2g k => mkApp (mkConst ``Base.dz2g) (mkNatLit k)
  | .stNZ k => mkApp (mkConst ``Base.stNZ) (mkNatLit k)
  | .stZ k => mkApp (mkConst ``Base.stZ) (mkNatLit k)

def projInt (b : Base) (f : Name) : MetaM Int := do
  let e := mkApp (mkConst f) (mkApp (mkConst ``Base.piece) (baseExpr b))
  let v ← whnf e
  let v ← instantiateMVars v
  unsafe evalExpr Int (mkConst ``Int) v


def baseTable : MetaM (Std.HashMap String BoxT) := do
  let mut m : Std.HashMap String BoxT := {}
  for b in allBases do
    m := m.insert (reprStr b) ⟨← projInt b ``Piece.a, ← projInt b ``Piece.b, ← projInt b ``Piece.lo,
      ← projInt b ``Piece.hi⟩
  return m


namespace Chk

def bxs (T : Std.HashMap String BoxT) (s : PSpec) : BoxT :=
  let B := T.getD (reprStr s.base) ⟨0, 0, 0, 0⟩
  ⟨B.a + s.vx, B.b + s.vx, B.lo + s.vy, B.hi + s.vy⟩

def farB (X Y : BoxT) : Bool :=
  decide (X.b + 2 < Y.a) || decide (Y.b + 2 < X.a) || decide (X.hi + 2 < Y.lo) ||
    decide (Y.hi + 2 < X.lo)

/-- uv-far: a box against an uv box (u1 u2 v1 v2), sufficient condition. -/
def farUV (X : BoxT) (u1 u2 v1 v2 : Int) : Bool :=
  decide (X.b - X.lo + 4 < u1) || decide (u2 + 4 < X.a - X.hi) ||
    decide (X.b + X.hi + 4 < v1) || decide (v2 + 4 < X.a + X.lo)

def wlBox (w : WL) (t : Int) : BoxT := ⟨w.px t - 1, w.px t + 3, w.py t - 1, w.py t + 3⟩
def sh (v : Int × Int) (X : BoxT) : BoxT := ⟨X.a + v.1, X.b + v.1, X.lo + v.2, X.hi + v.2⟩
def key (s : PSpec) : String := s!"{reprStr s.base} {s.vx} {s.vy} {s.ph}"

def routeFootXB : WL → List Corner → Nat → Nat → BoxT
  | g, [], T, i => wlBox g (T + i)
  | g, c :: cs, T, i =>
    if (T : Int) + i ≤ meetT g c - 20 then wlBox g (T + i)
    else if (T : Int) + i ≤ meetT g c + 40 then rxB c
    else routeFootXB (reflect g c).2 cs ((meetT g c).toNat + 40)
      (T + i - ((meetT g c).toNat + 40))

def entryFootB (p : Program) (a t : Nat) : List BoxT :=
  (List.range (t + 1)).flatMap fun j =>
    [sh (unitDX p a - 35 * t + 35 * j, unitDY p a - 64 * t + 64 * j) ⟨0, 90, -6, 38⟩,
     sh (unitDX p a - 35 * t + 35 * j, unitDY p a - 64 * t + 64 * j) ⟨49, 73, 36, 60⟩]

def linkFootWB (p : Program) (a t : Nat) (g : WL) (cs : List Corner) (T T0 j : Nat) :
    List BoxT :=
  if T + j ≤ routeEndX g cs T then [routeFootXB g cs T j]
  else if T + j + 16 ≤ T0 then [wlBox (route g cs).2 ((T : Int) + j)] else entryFootB p a t

def gateBoxB (p : Program) (r : Nat) : BoxT := sh (modDX p r - 1132, modDY p r - 1291) ⟨0, 90, 0, 60⟩

def modFootWB (p : Program) (r : Nat) (k : Int) (Tg j : Nat) : BoxT :=
  if j ≤ 134 then gateBoxB p r
  else if j ≤ 871 then wlBox (gateOutWL p r k) ((Tg : Int) + j)
  else if j ≤ 931 then rxB (rfJCorner p r)
  else wlBox (rfJOutWL p r k) ((Tg : Int) + j)

def rfJSpec (p : Program) (r : Nat) : PSpec := ⟨.rf 4, modDX p r - 850, modDY p r - 1044, 25⟩

def incRunStr : String := "-1395,-1387,-738,-716,-679,-649,-2133,-2103;-1329,-1321,-981,-959,-370,-340,-2310,-2280;-1100,-1010,-1100,-1068,-32,90,-2200,-2078;-945,-855,-918,-886,-59,63,-1863,-1741;-873,-865,-1210,-1188,315,345,-2083,-2053;-857,-804,-1105,-1052,195,301,-1912,-1906;-857,-804,-1105,-1052,196,300,-1910,-1907;-843,-753,-1464,-1432,589,711,-2307,-2185;-843,-753,-1143,-1102,259,390,-1986,-1855;-835,-813,-1489,-1481,646,676,-2324,-2294;-808,-718,-1402,-1370,562,684,-2210,-2088;-791,-86,-1104,-400,311,316,-1895,-486;-791,-86,-1104,-400,312,315,-1895,-486;-700,-678,-1476,-1468,768,798,-2176,-2146;-651,-643,-1427,-1405,754,784,-2078,-2048;-560,-528,-587,-497,-63,59,-1147,-1025;-498,-466,-552,-462,-36,86,-1050,-928;-347,-331,-107,-79,-268,-224,-454,-410;-347,-330,-101,-79,-268,-229,-448,-409;-333,-287,-151,-105,-228,-136,-441,-435;-333,-82,-355,-105,-227,273,-439,-436;-332,-267,-89,-23,-246,-241,-421,-290;-332,-60,-89,183,-245,-242,-421,122;-289,-199,-238,-148,-141,39,-440,-434;-274,-252,-806,-798,524,554,-1080,-1050;-269,-238,-25,6,-247,-241,-294,-232;-240,-232,3,11,-246,-241,-237,-221;-235,-226,9,18,-247,-241,-226,-208;-228,-185,16,58,-246,-241,-212,-127;-201,-82,-355,-236,35,273,-440,-435;-187,-171,56,72,-246,-240,-131,-99;-174,-135,70,108,-246,-241,-104,-27;-137,-60,106,183,-246,-240,-31,123;-121,-31,-402,-353,232,371,-523,-384;-101,-11,180,221,-322,-191,79,210;-94,128,-98,132,-226,226,-192,260;-94,128,-79,152,-246,207,-173,280;-86,49,-341,-285,199,390,-427,-236;-79,11,627,659,-738,-616,548,670;-71,-53,-356,-339,283,288,-427,-392;-71,-53,-356,-339,284,287,-427,-392;-69,-51,-355,-338,284,289,-424,-389;-69,-51,-355,-338,285,288,-424,-389;-50,-2,135,182,-232,-137,130,135;-50,-2,135,182,-232,-137,131,134;-47,-30,-250,-222,175,220,-297,-252;-33,9,-289,-248,215,298,-283,-278;-33,9,-289,-248,215,298,-282,-279;-32,57,-232,-142,197,202,-264,-85;-32,57,-232,-142,198,201,-264,-85;-29,3,350,440,-469,-347,321,443;-28,-7,-287,-266,256,262,-315,-273;-28,-7,-287,-266,258,261,-314,-274;-9,19,-269,-252,243,288,-278,-233;-9,113,-136,-95,86,249,-145,18;-5,113,-144,-96,91,257,-149,17;9,32,-290,-267,276,322,-260,-255;9,32,-290,-267,276,322,-259,-256;28,50,376,384,-356,-326,404,434;45,50,148,153,-106,-100,193,203;45,138,148,240,-104,-101,194,378;45,138,148,241,-104,-101,194,378;45,138,148,241,-104,-101,194,379;48,147,139,238,-107,-75,187,385;54,144,139,228,-86,-83,193,372;54,144,139,229,-86,-83,193,372;54,144,139,229,-86,-83,193,373;58,151,150,242,-93,-90,208,392;58,151,150,242,-93,-90,208,393;58,151,150,243,-93,-90,208,393;463,471,-69,-47,510,540,394,424;543,633,-23,9,534,656,520,642;578,668,-85,-53,631,753,493,615"

def incRunBUs : List (List Int) :=
  (incRunStr.splitOn ";").map fun t => (t.splitOn ",").map String.toInt!

deriving instance Repr for BoxT

def incRunB (p : Program) (r : Nat) : List (BoxT × List Int) :=
  incRunBUs.map fun l => match l with
    | [a, b, lo, hi, u1, u2, v1, v2] =>
      (sh (modDX p r, modDY p r) ⟨a, b, lo, hi⟩, [u1 + U p r, u2 + U p r, v1, v2])
    | _ => (⟨0, 0, 0, 0⟩, [])

def farBU (X : BoxT) (Y : BoxT × List Int) : Bool :=
  farB X Y.1 || match Y.2 with
    | [u1, u2, v1, v2] => farUV X u1 u2 v1 v2
    | _ => false

structure Ctx where
  p : Program
  i : Nat
  r : Nat
  P : IncPlan p i r
  LC : List PSpec
  LI : List PSpec

def mkCtx (p : Program) (i r : Nat) : Ctx :=
  let P := incPlan p i r
  { p, i, r, P,
    LC := (route (unitWL p i incDWL) P.csC).1 ++ chainSpecs (P.tc + 1) (unitDX p (i + 1)) (unitDY p (i + 1))
    LI := (route (unitWL p i incRWL) P.csR).1 ++
      chainSpecs (P.tl + 1) (unitDX p (mergeUnit p r)) (unitDY p (mergeUnit p r)) ++
      (route P.gM P.csM).1 ++ [incGateSpec p r, rfJSpec p r] ++
      groupSpecs ((List.range 28).map Base.dz2g) (modDX p r) (modDY p r) }

def contMov (c : Ctx) (j : Nat) : List BoxT :=
  let P := c.P
  if j ≤ P.Tc - 2010 then linkFootWB c.p (c.i + 1) P.tc (unitWL c.p c.i incDWL) P.csC 2010 P.T0c j
  else [sh (unitDX c.p (c.i + 1), unitDY c.p (c.i + 1))
    (wlBox chainOutWL (-166 + ((j - (P.Tc - 2010) : Nat) : Int)))]

def earlyMov (c : Ctx) (j : Nat) : List BoxT :=
  let P := c.P
  if j ≤ P.T1 - 2010 + (P.eM - P.T1) then
    (if j ≤ P.T1 - 2010 then
      linkFootWB c.p (mergeUnit c.p c.r) P.tl (unitWL c.p c.i incRWL) P.csR 2010 P.T0l j
    else [routeFootXB P.gM P.csM P.T1 (j - (P.T1 - 2010))])
  else if j + 16 ≤ P.Tg - 2010 then
    [wlBox (route P.gM P.csM).2 ((P.eM : Int) + ((j - (P.T1 - 2010 + (P.eM - P.T1)) : Nat) : Int))]
  else [gateBoxB c.p c.r]

/-- moving part of incFoot (strips omitted; after the module part: the run region). -/
def incMov (c : Ctx) (j : Nat) : List (BoxT × List Int) :=
  let P := c.P
  if j ≤ P.Tg - 2010 then (earlyMov c j).map (·, [])
  else if j - (P.Tg - 2010) ≤ 946 then [(modFootWB c.p c.r P.km P.Tg (j - (P.Tg - 2010)), [])]
  else incRunB c.p c.r

def far1 (T : Std.HashMap String BoxT) (X : BoxT) (Ys : List PSpec) : List String :=
  Ys.filterMap fun s => if farB X (bxs T s) then none else some (key s)

def rng (a b : Nat) : List Nat := (List.range (b - a)).map (· + a)

def report (name : String) (bad : List String) : IO Unit := do
  if bad.isEmpty then IO.println s!"  {name}: ok"
  else IO.println s!"  {name}: FAIL {bad.length}: {bad.take 6}"

def check (T : Std.HashMap String BoxT) (nm : String) (c : Ctx) : IO Unit := do
  let p := c.p
  let P := c.P
  IO.println s!"{nm} i={c.i} r={c.r} T0c={P.T0c} T0l={P.T0l} T1={P.T1} eM={P.eM} Tg={P.Tg} Tend={P.Tend} endC={routeEndX (unitWL p c.i incDWL) P.csC 2010} endR={routeEndX (unitWL p c.i incRWL) P.csR 2010}"
  -- flyC
  let eC := routeEndX (unitWL p c.i incDWL) P.csC 2010
  report "flyC" ((rng eC (P.T0c - 16)).flatMap fun j =>
    (far1 T (wlBox (route (unitWL p c.i incDWL) P.csC).2 j) c.LC).map (s!"j={j} " ++ ·))
  report "outC" ((rng 0 166).flatMap fun j =>
    (far1 T (sh (unitDX p (c.i + 1), unitDY p (c.i + 1)) (wlBox chainOutWL (-166 + (j : Int)))) c.LC).map
      (s!"j={j} " ++ ·))
  let eR := routeEndX (unitWL p c.i incRWL) P.csR 2010
  report "flyR" ((rng eR (P.T0l - 16)).flatMap fun j =>
    (far1 T (wlBox (route (unitWL p c.i incRWL) P.csR).2 j) c.LI).map (s!"j={j} " ++ ·))
  report "flyM" ((rng P.eM (P.Tg - 16)).flatMap fun j =>
    (far1 T (wlBox (route P.gM P.csM).2 j) c.LI).map (s!"j={j} " ++ ·))
  report "gate" (far1 T (gateBoxB p c.r) (c.LI.filter fun s => key s != key (incGateSpec p c.r)))
  report "fl1" ((rng 134 871).flatMap fun j =>
    (far1 T (wlBox (gateOutWL p c.r P.km) ((P.Tg : Int) + j)) c.LI).map (s!"j={j} " ++ ·))
  report "rf" (far1 T (rxB (rfJCorner p c.r)) (c.LI.filter fun s => key s != key (rfJSpec p c.r)))
  report "fl2" ((rng 931 946).flatMap fun j =>
    (far1 T (wlBox (rfJOutWL p c.r P.km) ((P.Tg : Int) + j)) c.LI).map (s!"j={j} " ++ ·))
  let grpKeys := (groupSpecs ((List.range 28).map Base.dz2g) (modDX p c.r) (modDY p c.r)).map key
  let nonGrp := c.LI.filter fun s => !(grpKeys.contains (key s))
  report "inc (run region vs non-circuit pieces)" ((incRunB p c.r).flatMap fun Y =>
    nonGrp.filterMap fun s => if farBU (bxs T s) Y then none else some s!"{reprStr Y.1} {key s}")
  -- entC / entR (proved; sanity)
  let chC := (chainSpecs (P.tc + 1) (unitDX p (c.i + 1)) (unitDY p (c.i + 1))).map key
  report "entC" ((entryFootB p (c.i + 1) P.tc).flatMap fun X =>
    far1 T X (c.LC.filter fun s => !(chC.contains (key s))))
  let chR := (chainSpecs (P.tl + 1) (unitDX p (mergeUnit p c.r)) (unitDY p (mergeUnit p c.r))).map key
  report "entR" ((entryFootB p (mergeUnit p c.r) P.tl).flatMap fun X =>
    far1 T X (c.LI.filter fun s => !(chR.contains (key s))))
  -- body
  let bodyKeys := (groupSpecs ((List.range 3).map Base.bodyInc) (unitDX p c.i) (unitDY p c.i)).map key
  let M := machSpecs p
  report "body" (far1 T (sh (unitDX p c.i, unitDY p c.i) ⟨113, 354, 61, 286⟩)
    (M.filter fun s => !(bodyKeys.contains (key s))))
  -- threads (strips omitted: lane fields, proved)
  let N := P.Tend - 2010
  let staticCI := c.LC.flatMap fun s => far1 T (bxs T s) c.LI
  report "threads (static pieces)" staticCI
  let mut bad : List String := []
  let mut j := 0
  while j < N do
    let cm := contMov c j
    let im := incMov c j
    for X in cm do
      for s in c.LI do
        if !(farB X (bxs T s)) then bad := s!"j={j} contMov {reprStr X} vs I {key s}" :: bad
      for Y in im do
        if !(farBU X Y) then bad := s!"j={j} contMov {reprStr X} vs incMov {reprStr Y.1}" :: bad
    if j ≤ P.Tg - 2010 + 946 then
      for Y in im do
        for s in c.LC do
          if !(farB (bxs T s) Y.1) then bad := s!"j={j} C {key s} vs incMov {reprStr Y.1}" :: bad
    j := j + 1
  -- run region vs LC (static, once)
  for Y in incRunB p c.r do
    for s in c.LC do
      if !(farBU (bxs T s) Y) then bad := s!"run {reprStr Y.1} vs C {key s}" :: bad
  report "threads (moving)" bad.reverse
  -- idle: all distinct moving boxes and thread pieces vs idle pieces
  let thr := (c.LC ++ c.LI).map key
  let idle := M.filter fun s => !(thr.contains (key s))
  let mut boxes : Std.HashSet (Int × Int × Int × Int) := {}
  j := 0
  while j < N do
    for X in contMov c j do boxes := boxes.insert (X.a, X.b, X.lo, X.hi)
    if j ≤ P.Tg - 2010 + 946 then
      for Y in incMov c j do boxes := boxes.insert (Y.1.a, Y.1.b, Y.1.lo, Y.1.hi)
    j := j + 1
  for s in c.LC ++ c.LI do boxes := boxes.insert ((bxs T s).a, (bxs T s).b, (bxs T s).lo, (bxs T s).hi)
  let mut grid : Std.HashMap (Int × Int) (List PSpec) := {}
  for s in idle do
    let B := bxs T s
    for gx in rng 0 ((((B.b + 3) / 128) - ((B.a - 3) / 128) + 1).toNat) do
      for gy in rng 0 ((((B.hi + 3) / 128) - ((B.lo - 3) / 128) + 1).toNat) do
        let k := ((B.a - 3) / 128 + gx, (B.lo - 3) / 128 + gy)
        grid := grid.insert k (s :: grid.getD k [])
  let mut badI : List String := []
  for (a, b, lo, hi) in boxes.toList do
    let mut cand : List PSpec := []
    for gx in rng 0 (((b / 128) - (a / 128) + 1).toNat) do
      for gy in rng 0 (((hi / 128) - (lo / 128) + 1).toNat) do
        cand := grid.getD (a / 128 + gx, lo / 128 + gy) [] ++ cand
    for s in cand do
      if !(farB ⟨a, b, lo, hi⟩ (bxs T s)) then
        badI := s!"box {a} {b} {lo} {hi} vs idle {key s}" :: badI
  for Y in incRunB p c.r do
    for s in idle do
      if !(farBU (bxs T s) Y) then badI := s!"run {reprStr Y.1} vs idle {key s}" :: badI
  badI := badI.eraseDups
  report s!"idle ({boxes.size} boxes, {idle.length} idle pieces)" badI

def progs : List (String × Program) :=
  [("inc0halt", [.inc 0, .halt]),
   ("add", [.decJz 0 3, .inc 1, .decJz 2 0, .halt]),
   ("share", [.inc 0, .decJz 0 3, .decJz 0 3, .halt]),
   ("rand", [.inc 2, .decJz 0 4, .inc 1, .decJz 1 6, .inc 0, .decJz 1 3, .halt]),
   ("incs", [.inc 0, .inc 1, .inc 0, .inc 2, .inc 0, .halt])]

def incsOf (p : Program) : List (Nat × Nat) :=
  (List.range p.length).filterMap fun i => match p[i]? with
    | some (Instr.inc r) => some (i, r)
    | _ => none

def main (T : Std.HashMap String BoxT) (sel : List String) : IO Unit := do
  for (nm, p) in progs do
    if sel.contains nm then
      for (i, r) in incsOf p do
        check T nm (mkCtx p i r)
        (← IO.getStdout).flush

end Chk

#eval show MetaM Unit from do
  let T ← baseTable
  Chk.main T ["add", "share", "rand", "incs"]
