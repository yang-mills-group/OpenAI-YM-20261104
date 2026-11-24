import YM.MergeProof.North.Frost
import YM.RG05.Strand.Difference
/-! # A mixed source mode: capture at ANY member, no loss in the support exponent

 Adaptation of the Frost (`pinch`/`sprouts`) technique; need a result BEFORE
 moving individual anchors or changing the layout. Rather than `Cordons`
 grouping of the *whole* poly to bind two sources (which has a price depending
 on their geometry), spend at any one anchoring site and restrict to *words
 containing it* from `diced`. Then by `Loon`'s `petals` and `pillars`
 read directly to the actual accessible leaf system (same R). -/
noncomputable section
set_option autoImplicit false
namespace YM.RG05.Strand
open Function Filter Lattice RG Wilson Pressure Finset MeasureTheory
open MergeProof Push Marker Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil Extra.Trajectories MergeProof.Float Ribbons
open scoped Topology BigOperators Classical
variable {V I : Type}[Fintype V][DecidableEq V][Fintype I]{B:Census V} {G:Gauge}{n:Side}
 {R:Rep G n}{a b: ℝ}{w:V→ℝ}

lemma precinct (v:V)(a': B.Mode)(ha:v ∈ a'.val) {o : V→Site n}{X:I→Support n}{P:BudgetPoint}{F:I→ Config G n→ Poly B} (hq:∀ i,Borne o (X i) (F i) P.threshold) (hr:Towed w X F P.B P.supportExponent a)(hw:∀ i,0<w i):∃ f:I→ℝ, (∀ j U, ‖(F j U).part a'‖ ≤ f j)∧ ∑ j,P.mass (X j) (f j) ≤ a/Poly.toll w a':=by
    obtain ⟨x,hh,hX,hV⟩:= Salt.diced F X w P.supportExponent a P.B hw hr
    let f j := if o v∈ X j then x (j,a') else 0
    have hx:= Poly.worth hw a'
    refine ⟨f,fun j U=>?_, (le_div_iff₀ hx).mpr ?_⟩
    · unfold f; split; next=> exact hX (j,a') U
      next hz => rw [show (F j U).part a'=0 from ?_,norm_zero]; exact Classical.byContradiction fun h=> hz ((hq j).place _ U h (mem_image_of_mem _ ha))
    have ht:= hV (o v); let g(j):=P.mass (X j) (f j)*Poly.toll w a'
    have hp:=Budget.pull_le (q:=fun j:I=>(j,a')) (p:=fun _=>True) ht (?_ : ∀ j,0≤g j) (fun _ _=> trivial) (show Set.InjOn _ _ from (show Function.Injective (fun j:I=>(j,a')) from fun _ _ h => Prod.mk.inj h|>.1).injOn) ?_
    · rw [Finset.sum_mul]; exact Budget.cap hp univ
    · intro j; apply mul_nonneg _ hx.le; apply mul_nonneg (Real.exp_pos _).le; unfold f; split; exact hh _; rfl
    intro i _; unfold g; apply le_of_eq; unfold BudgetPoint.mass f; dsimp only [Function.comp_apply]; split_ifs <;> ring
variable {o:V→Site n} {F : Support n→ Config G n→Poly B}{K:Box n→ Config G n→Poly B}
lemma environs (v:V)(a': B.Mode)(ha:v∈ a'.val)(A: Menu.Arsenal R)(hF:∀ i,Burns o i (F i) R.p.threshold)(hK:∀ i,Flow o i (K i) R.p.threshold)(ht:Towed w id F R.p.B R.p.supportExponent a)(hh:Towed w Prod.fst K R.p.B R.p.supportExponent b)(hw:∀ i,0<w i): Blade R (o v) (fun U=>(∑ i,F i U).part a') (fun j U=>(K j U).part a') 0 (2*(a/Poly.toll w a')+2*(b/Poly.toll w a')):=by
    let f i U:= (F i U).part a'; let g i U:= (K i U).part a'
    obtain ⟨x,hx,hT⟩:= precinct v a' ha (fun i=> (hF i).toBorne) ht hw; obtain ⟨y,hy,hJ⟩:= precinct v a' ha (fun i=>(hK i).toBorne) hh hw
    have he(i: Support n): Blade R (o v) (f i) 0 0 (2*R.p.mass i (x i)) := by
       let h:= hF i|>.toBorne
       apply MergeProof.Float.petals A _ _ (fun k U=> congr_arg (fun f=>Poly.part f a') (h.turns k U)) (h.me _) (fun U V he ht=>congr_arg (fun f=>Poly.part f a') (h.home _ _ he ht)) (fun U H=> (hF i).permits U (fun hi=>H (by rw [hi];rfl))) (fun hh=>?_) (hx i)
       obtain ⟨U,hU⟩:= Function.ne_iff.mp hh; apply h.place _ _ hU; exact mem_image_of_mem _ ha
    have hp(i:Box n): Blade R (o v) 0 (Pi.single i (g i)) 0 (2*R.p.mass i.1 (y i)):=by
       let h:= hK i|>.toBorne
       apply MergeProof.Float.pillars A i _ (fun k U=>congr_arg (fun f=>Poly.part f a') (h.turns k U)) (h.me _) (fun U V he ht=> congr_arg (fun f=>Poly.part f a') (h.home U V he ht)) (fun U H=> (hK i).permits U (fun hi=>H (by rw [hi]; rfl))) (fun hh=>?_) (hy i)
       obtain ⟨U,hU⟩:= Function.ne_iff.mp hh; apply h.place _ _ hU; exact mem_image_of_mem _ ha
    have h: (fun U=>(∑ i,F i U).part a')=∑ i,f i:= by funext; rw [Finset.sum_apply,Poly.part_sum]
    have ht:= (comp_many f _ _ _ Finset.univ (fun i _=> he i)).comp (comp_many _ _ _ _ Finset.univ (fun i _=>hp i))
    simp only [sum_const_zero,add_zero,MergeProof.Float.supple g,zero_add, ← Finset.mul_sum] at ht
    rw [h]; exact ht.more (add_le_add (mul_le_mul_of_nonneg_left hT zero_le_two) (mul_le_mul_of_nonneg_left hJ zero_le_two))
end YM.RG05.Strand
