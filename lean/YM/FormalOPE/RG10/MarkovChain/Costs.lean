import YM.FormalOPE.RG10.MarkovChain.Band
/-!
 # every unmasked hierarchy price depends only on two successive rows while gauged.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.MarkovChain
open Function Filter Topology Set MeasureTheory PertExtension Precision
open BlockGauge Inherit Push.Loops Chart Lattice RG GaussianScore
open YM.PertExtension.Series YM.PertExtension.Series.Tested YM.PertExtension.Series.Radial
open StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius
open Line
variable {G: Gauge}{c f n:Side}
variable {L: Fabric G n} (T:Cloth L)
namespace Roof
 def realTop (x:Field T.choose): L.LinksOn:= T.choose.board (expLinks G T.choose.Bulk x)
 def outside_core (i:L.Cost) (x:Field T.choose):=L.regional (realTop T x) i
lemma blockRoof {n}{L:Fabric G n}(T:Cloth L)(i:L.Cost): Roof T (outside_core T i):= by
 cases T with
 | floor=> trivial
 | @inLayer c f S H t hf L P C=>
    let d:= sector S H t hf L P C.choose
    change Option _ at i
    cases i with
    | none=>
     apply onlyNow (a:=(outside_core _ _)); intro x y z h
     change (penalty S t ((Fabric.layer S H t hf L).principal ((P.join C.choose H t hf).board (expLinks G _ ((sector S H t hf L P C.choose) (x,y))))) (L.principal (future S H t hf L ((P.join C.choose H t hf).board (expLinks G _ ((sector S H t hf L P C.choose) (x,y)))))))=(penalty S t ((Fabric.layer S H t hf L).principal ((P.join C.choose H t hf).board (expLinks G _ ((sector S H t hf L P C.choose) (x,z))))) (L.principal (future S H t hf L ((P.join C.choose H t hf).board (expLinks G _ ((sector S H t hf L P C.choose) (x,z)))))))
     simp_rw [Line.future_eq,Line.portrayed, Line.first, h]
    | some i=>
      rw [show outside_core (Cloth.inLayer (t:=t) (b:=H) (h:=hf) P C) (some i)=(fun x=> outside_core C i ((d.symm x).2)) from ?_]
      exact liftLater S H t hf P C _ (blockRoof C i)
      ext1 x; change L.regional (future S H t hf L ((P.join C.choose H t hf).board (expLinks G (P.join C.choose H t hf).Bulk x))) i = _
      let y:=d.symm x
      conv_lhs => rw [← d.apply_symm_apply x];
      exact congr_arg (fun x=> L.regional x i) (Line.future_eq _ _ _ _ _ _ _ y.1 y.2) -- eta pair issue
termination_by structural T
 def cost_core (i:L.Accounts) (x:Field T.choose):=L.price (realTop T x) i
lemma vacuum (i:L.Accounts): Roof T (cost_core T i):= by
 cases i with
 | none => apply head; intro x y h; change wilson (L.principal _) = wilson (L.principal _); unfold realTop; rw [Line.portrayed,Line.portrayed,h]
 | some i=> exact blockRoof T i
 def hab (w:L.Accounts→ℝ) (u: Field T.choose):= L.spend w (realTop T u)
lemma habituate (w:L.Accounts→ℝ): Roof T (hab T w):= by
 rw [show hab T w=∑ i,w i • (cost_core T i) from funext fun x=> by simp [hab, Fabric.spend, Finset.sum_apply,cost_core]]
 apply billSum; intro i _; exact smul (vacuum T i) (w i)
end Roof
end YM.FormalOPE.RG10.MarkovChain
