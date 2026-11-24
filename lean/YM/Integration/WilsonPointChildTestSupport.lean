import YM.Integration.WilsonNeutralPointCourse

/-! The entire independently normalized pinned field reads its test jet at
    the actual nested child point. This includes every off-diagonal restamp. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPointChildTestSupport
open YM FormalBulk08 Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof Quire Dove Sierra
open PhysicalNext.Repeat.Legato Next.Foundations Borough
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open WilsonNeutralPointCourse
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{d D:ℕ}

def Same (a:Dawn.Pier)(q f:Studio D):Prop:=∀k:Brush D,q.val k a=f.val k a
def At (a:Dawn.Pier)(Y:Anthem D G):Prop:=∀q f,Same a q f→Y q=Y f

theorem rescale {L:Side}(x:Site L)(h:2≤L.val)(y:Dawn.Pier){q f:Studio D}
    (eq:Same (Dawn.peninsula x h y) q f):Same y (Dawn.throughW x D h q) (Dawn.throughW x D h f):=by
  intro k
  change (Dawn.tunnel x D h q).val k y=(Dawn.tunnel x D h f).val k y
  rw [Dawn.tunnel_show,Dawn.tunnel_show,eq k]

def points (R:Run G)(digit:∀j,Site (R.family.S.block j)):(steps j:ℕ)→Dawn.Pier
  | 0,_=>Dawn.origin
  | n+1,j=>Dawn.peninsula (digit j) (Elm.growL R.family.path.levels j) (points R digit n (j+1))

private theorem merge {F:Frame G d}(V:Plaza F D)(M:Tilework F)(a:Dawn.Pier)
    (each:∀b:Letter F,At a (V b))(s:Letter F):At a (larch V M s):=by
  intro q f same
  simp only [larch,Finset.sum_apply,Kemp.launch]
  apply Finset.sum_congr rfl
  intro b _
  rw [each b q f same]

theorem path (R:Run G)(wood:Primer.Families R.family)(a:hue G)(depth:d<D)
    (digit:∀j,Site (R.family.S.block j))(N h i:ℕ):
    ∀b:Letter (R.family.labels.level d),At (points R digit h i) (walk R wood a depth digit N h i b):=by
  induction h generalizing i with
  | zero=>
    intro b q f eq
    change Dawn.notch _ _ q • _=Dawn.notch _ _ f • _
    exact congrArg (fun c:ℝ=>c • paperback (R.family.localSection d) (mint _ b)) (eq _)
  | succ n ih=>
    intro b
    let Y:=walk R wood a depth digit N n (i+1)
    let V:=forward R wood a digit N i Y
    apply merge V _ _ _ b
    intro s q f hold
    have same:=rescale (digit i) (Elm.growL R.family.path.levels i) (points R digit n (i+1)) hold
    have agree:=ih (i+1) s _ _ same
    change _ • Sierra.enterStep _ _ _ _ _ _ _ (Kemp.work _ (Y s (Dawn.throughW (digit i) D _ q)))=
      _ • Sierra.enterStep _ _ _ _ _ _ _ (Kemp.work _ (Y s (Dawn.throughW (digit i) D _ f)))
    change Y s _=Y s _ at agree
    rw [agree]

theorem original (R:Run G)(wood:Primer.Families R.family)(a:hue G)(depth:d<D)
    (digit:∀j,Site (R.family.S.block j))(N i:ℕ)(b:Letter (R.family.labels.level d)):
    At (points R digit (N-i) i) (filed R wood a depth digit N i b):=
  path R wood a depth digit N (N-i) i b

end YM.Integration.WilsonPointChildTestSupport
