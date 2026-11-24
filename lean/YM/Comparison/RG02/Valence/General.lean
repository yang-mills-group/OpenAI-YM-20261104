import YM.Comparison.RG02.Valence.Mirror
/-! Fk rank implies genuine smoothness in ANY finite-dimensional circle of external fields.
    All-period jet statement on formal **moments**, no actual smoothness claims. -/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Valence
open Function Filter Finset MeasureTheory RG Precision Lattice Wilson Exterior Tree
open YM.Analysis YM.Marker YM.Multi Cumulants Cumulants.Wick Order Join Bulk Assembly
open YM.Extra.Trajectories (connected pass_connected)
open YM.Next.Rank
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {V : Type} [DecidableEq V] [Fintype V] {R : Census V} {r : ℕ}
variable {G : Gauge} {c f : Side} {S : StepData c f} {p : Clip} {P : PathData G} {O : ChartRatio G}
  (K : Bulk.Kernel S p P O) (F : Tree.Forest S.ratio) (w : S.Choices) (W : Bulk.Colors R G f) (x : fieldDir G c 1)
  (r:ℕ)
local notation "X"=> fieldDir G c 1
local notation "Ω" x => Fk K F w W x r

def costAll (t : Hot R→ℕ) (i : V) : ℤ:= ∑ v:Hot R,(t v:ℤ)+iweight i
where iweight (_ : V):ℤ:=0
omit [Fintype V] in
lemma every (t : Hot R→ℕ) (u : R.Mode) : Toile t u (costAll t):= by
   intro p _; unfold costAll at *; simp_rw [costAll.iweight, add_zero]
   obtain ⟨i,hi⟩:=p.property; have he (i:V) (h:i∈p.sites): 0 ≤ ∑ v:Hot R,(t v:ℤ):= sum_nonneg fun i _=>by positivity
   have h : ((t p):ℤ) ≤ ∑ v:Hot R,(t v:ℤ):= single_le_sum (fun i (_:i∈univ)=>show 0≤(t i:ℤ) from by positivity) (mem_univ p)
   exact le_trans (le_trans h (single_le_sum he hi)) (le_add_of_nonneg_left (by norm_num))

lemma entire (i:(Board R r).Mode) : ContDiff ℝ ω (fun x:X=> (connected (Ω x)).part i):= by
   let s:= Join.right i
   let p:= Join.left i
   have hi:=every W.power p
   have he(x:X): (connected (Ω x)).part i= (s.val.card.factorial:ℂ)*(observe R r (connected (Ω x)) s.val.card).part p := by
      exact (pair_reunite i ▸ ((fk_sym K F w W x r).log (fk_unit ..)|>.observe_part p s).symm)
   simp_rw [he]; apply contDiff_const.mul; exact (read p K F w W _ s.val.card hi (r:=r)).smooth

lemma moments_smooth (i : (Board R r).Mode) : ContDiff ℝ ω (fun x:X=> (Ω x).part i):= by
    let A(x:X):=Ω x; have h(x:X): (A x).part i=∑ s∈shards (Board R r) i,∏ t∈s.val,(connected (Ω x)).part t.val :=by
       nth_rw 1 [show A x=(connected (Ω x)).pass from (pass_connected (fk_unit K F w W x r)).symm]; exact pass_partition _ (Extra.Trajectories.connected_quiet (fk_unit K F w W x r)) i
    change ContDiff ℝ ω (fun x:X=> (A x).part i); simp_rw [h]; apply ContDiff.sum; intro b _; exact contDiff_prod fun a _=> entire K F w W r a.val
lemma moment_record (i:R.Mode) (k:ℕ) : ContDiff ℝ ω (fun x:X=> (observe R r (Ω x) k).part i):= by
   unfold observe; split
   next h=> simp_rw [Poly.part_smul]; exact contDiff_const.mul (moments_smooth K F w W r (pair i (pick r k)))
   next h=> exact contDiff_const
end YM.Comparison.RG02.Valence
