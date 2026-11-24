import YM.LocalLTE.Slide.Carving
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false
namespace YM.PhysicalNext.Repeat.Scarf
open Function Filter Set Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Poll Pond MeasureTheory ProbabilityTheory Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Metric Progress.DirectedRecipe Payments Ovens Ovens.Pipes
open Refrain Trio Marlin Push.BetaTransport Shingle
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c L:Side} {X : Listing G c} {m r j k p:ℕ} {e d a Z K q b v Y : ℝ} {x:ℝ} {S:Set ℝ} {ι:Type}
-- primary ornament site widened, still full K mass allocation ONLY eligibility. Frame output may use m beyond (2*z) with flag tests.F.work
variable (B:BudgetPoint)(X : Listing G c) (s : Finset ℕ) (m : ℕ)

-- spin preserving. Assignment for Tape continuity.
variable {X s m B}
lemma rotation {V:Collection.Source G c} (θ:Signed)(x:Site c)(M:(X.read V).Moves θ x) (he:∀ i,i∈s ↔ M.ep i∈s): Nonempty (((diamond X s m).read V).Moves θ x):=by
   let Y:=diamond X s m; refine ⟨⟨M.ep,M.kp,(fun i=>?_),(fun i=>?_),M.forced_support,M.forced_inventory,M.forced_tests,M.valuesE,M.valuesK⟩⟩
   · change (enlarged X.reg s m _).site=Lattice.affine θ x (enlarged X.reg s m _).site; rw [homeland,homeland]; exact M.reg_site i
   change (Scarf.enlarged X.reg s m (M.ep i)).support=(Scarf.enlarged X.reg s m i).support.image _; unfold enlarged; by_cases hi:i∈s; swap; · rw [if_neg hi,if_neg (not_congr (he i)|>.1 hi)]; exact M.reg_support _
   rw [if_pos hi,if_pos ((he i).1 hi)]; exact (normRange (s:=(θ,x)) (M.reg_site i) _).symm
lemma transfer {T:Set ℝ}{t:ℝ→ Collection.Source G c} (h:Compared X B t T)(he:Rooms X.reg s m B p) : Compared (diamond X s m) B t T:=by
   let V x:=(diamond X s m).read (t x); let C:=(diamond X s m)
   have hQ i : (C.reg i).site=(X.reg i).site:= homeland _ _ _ _
   have hF i : (X.reg i).support⊆ (C.reg i).support:= placed X.reg s m B he i
   refine ⟨fun x hx=> ⟨fun i ε hp=>?_,(h.values x hx).2⟩,fun x hx u hk=>?_⟩
   · filter_upwards [(h.values x hx).1 i ε hp] with y hy; refine ⟨hy.1,fun v hv l hl hd=> hy.2 v (healthy_mono (hF i) hv) l hl (?_)⟩
     exact hQ i ▸ hd -- edit
   obtain ⟨v,e,f,ht,hE,hD,hp,hΓ⟩:= h.series x hx u hk
   have hh i (he:Majorizes B e f (X.read (t i))): Majorizes B e f (C.read (t i)):= by
      refine ⟨fun i=> ?_,he.hard⟩; change B.supBounds (C.reg i).site (C.reg i).support _ _; rw [hQ]; exact VerifiedReset.sup_larger (he.smooth i) (hF i)
   exact ⟨v,e,f,ht,hE,hD,hh _ hp,hΓ.mono fun x hu=> hh _ hu⟩
lemma hesitating {T:Set ℝ}{t :ℝ→ Collection.Source G c} (h:Compared X B t T)(hR:Rooms X.reg s m B p) {d g: ℝ→ Offer G c} {z:ℕ}
    (hh:z≤ m) (hm:∀ i,Shingle.Mild B (neighbors z i) (fun x=> g x i) T) (he:∀ x∈T,∀ i, B.Regular (X.reg i).support ((t x).logRead i)) (i:Site c)(hx:x∈T) (hk:Varies (fun y=>d y i) x T):
    Varies (fun x=> hesitates B X s m z (t x) (d x) (g x) i) x T:=by
    have hv : Varies (fun x=> delay X.reg s m B (t x).logRead i) x T:= flowSap X.reg s m B hR i hx (t:=fun x=> (t x).logRead) (fun i _=> Shingle.litIn X i h (fun x hx=>he x hx _))
    exact (hk.add hv).add (((hm i).clipped x hx).sub (((hm i).mono (show neighbors z i⊆neighbors m i from fun j hj=> (neighbors_mem ..).mpr (((neighbors_mem ..).1 hj).trans hh))).clipped x hx))
end YM.PhysicalNext.Repeat.Scarf
