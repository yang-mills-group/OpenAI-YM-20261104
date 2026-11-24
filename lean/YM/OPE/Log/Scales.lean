import YM.OPE.Log.Peak
/-! # Compensated estimates and quantitative unselected + all selected -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log
open Function Set Filter Metric Lattice RG Wilson
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book} (U:Spec.Final C F S) {I J L:Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J]
    (p:I→ C.book.Token)(q:J→ C.book.Token) (n:ℕ) (h: Services C F S)
    {𝓕: Filter (ℕ×ℕ)}[𝓕.NeBot]{W r' D} (L': LogPackage C W r' D) (hM:𝓕 ≤ F.fuse)(hV:MatrixTicket (C:=C) S U.sector.derivatives 𝓕)
    {P:Prescription U.sector.derivatives}(hP:P.Coherent){l: Filter L}[l.NeBot]
    {r:L→ℝ}(hr:Tendsto r l (𝓝[>]0))
    {x:L→I→ E4}{z:L→E4}{y:L→J→ E4} {M c η:ℝ} (hm:0≤ M)(hη:0<η) (hx:∀ᶠ i in l,WithinRoom (r i) M η (x i) (z i))
local notation "T"=> (fun i=> run (r i))
local notation "D'"=> U.sector.derivatives
local notation "g!"=> (fun i=> groundError U P n (x i) p (z i) (y i) q)
lemma transport {r M η:ℝ}(u:I→E4)(z:E4)(h:WithinRoom r M η u z) : WithinRoom r M η (OPE.away u z) 0:=by
    refine ⟨fun i=>?_,fun i j hij=>?_⟩; · simpa only [OPE.away,sub_zero] using h.span i
    unfold OPE.away; rw [sub_sub_sub_cancel_right]; exact h.spaced _ _ hij
include U h in
lemma spectators (hc:0<c) (v:C.book.Token) : ∃ a:ℝ, ∀ (y:J→ E4)(z:E4), ClearOf z y c → ‖viewing U (beside (sole z) y) (beside (sole v) q)‖ ≤ a:=by
    by_contra! hf; choose y z hy hz using fun n:ℕ => hf (Real.exp (n:ℝ)+0)
    let u (i):= viewing U (beside (sole (z i)) (y i)) (beside (sole v) q); have ht:= tendsto_natCast_atTop_atTop (R:=ℝ); let x (i:ℕ):=(i:ℝ)
    obtain ⟨hp,hq⟩:= free_clear ht hc (Eventually.of_forall hy); have he:= phase_budget U h.schedule (sole v) q ht (Kept.sole _ _ _ _) hp hq le_rfl le_rfl (1:ℝ) (by ring_nf; norm_num)
    obtain ⟨i,hi⟩ := he.exists; have hv : ‖u i‖ ≤ Real.exp (i:ℝ):=(by simpa [u] using hi); linarith only [hv,show Real.exp (i:ℝ)+0 < ‖u i‖ from hz i]

private lemma cong_norm (u:ℂ)(x:U.α.unselected.algebra): ‖u • x‖ = ‖u‖*‖x‖:=by haveI : IsClosed (U.α.unselected.algebra : Set U.α.room.VacuumOp) := isClosed_closure; letI := StarSubalgebra.cstarAlgebra U.α.unselected.algebra; exact norm_smul u x
include h L' hM hV hP hm hη hr hx U
lemma compensated_coeff (i: Mode D'): Wallet l T (fun t=> (r t^sigma p/r t^i.fst:ℝ) • P.ope i (x t) p (z t)) :=by
    cases isEmpty_or_nonempty I with
    | inl hI=>
       simp_rw [empty_coeff P p _ _ U.room.kernel]; rw [show sigma p=0 from (by unfold sigma; simp)]; rcases Nat.eq_zero_or_pos i.fst with hz|hz;
       · simpa only [hz,pow_zero,div_self one_ne_zero,one_smul] using (Wallet.const (run_towards hr) (P.test i 0 (S.unit 0)))
       simp_rw [Prescription.highVan U.room.kernel.laws.toSymmetric U.phase.transport.injection hP i hz,smul_zero]; exact Wallet.const (run_towards hr) (0:ℂ)
    | inr hI=>
       let u (i):= OPE.away (x i) (z i); apply (interpolated U hr p L' h.simpleGate hM hV i hP hI.some hη h.schedule (hx.mono fun j hj=> transport (x j) _ hj) hm).congr; refine Eventually.of_forall fun t=> ?_; change _ • P.ope i _ p 0= _; rw [show P.ope i _ p 0 = _ from (show P.ope i (u t) p 0 = P.ope i (x t) p (z t) from (by simpa only [sub_self] using ope_away P p (x t) (z t) (z t) i))]

set_option maxHeartbeats 400000 in
lemma ground_plus (hc:0<c)(hy:∀ᶠ i in l, ClearOf (z i) (y i) c): Wallet l T (fun i=> r i ^ sigma p/r i^(n+1)*‖groundError U P n (x i) p (z i) (y i) q‖):=by
    obtain ⟨he,hE⟩:=room_regime hr hm hη hx; have ht:=run_towards hr; obtain ⟨hf,hF⟩:= free_clear ht hc hy; let Y(i):=r i^sigma p/r i^(n+1); have hu:RateIs l T Y ((n+1:ℝ)-sigma p):= (((loglife hr).power (sigma p)).div ((loglife hr).power (n+1))).swap (by push_cast; ring)
    have hh:= arrangement_cost U P (n+1) p q ht h hP he hE zero_lt_one hf hF le_rfl le_rfl zero_lt_one; let G(i):= groundError U P (n+1) (x i) p (z i) (y i) q; have hG:= Wallet.of_strict ht ((hu.pays ht).mul hh.norm) (by push_cast; linarith only)
    let z₀ (w:Mode D') i := P.ope w (x i) p (z i) • viewing U (beside (sole (z i)) (y i)) (beside (sole (P.letter w)) q); let V:= bands D' (n+1)\ bands D' n;
    have hv:∀ w∈V, Wallet l T (fun i=> Y i*‖z₀ w i‖):=by
       intro w hw; obtain ⟨a,ha⟩:= spectators U q h hc (P.letter w); have he:w.fst=n+1:= le_antisymm ((full_bands ..).1 (Finset.mem_sdiff.mp hw).1) (lt_of_not_ge (fun hh=>(Finset.mem_sdiff.mp hw).2 ((full_bands ..).2 hh)))
       apply (((compensated_coeff U p h L' hM hV hP hr hm hη hx w).norm).mul (Wallet.absolute ht a (f:=fun i=> ‖viewing U (beside (sole (z i)) (y i)) (beside (sole (P.letter w)) q)‖) (by filter_upwards [hy] with i hi; rw [Real.norm_of_nonneg (norm_nonneg _)]; exact ha _ _ hi))).congr; filter_upwards [hu.pos] with i hi; unfold Y z₀; rw [norm_smul,he,Real.norm_of_nonneg hi.le, cong_norm U]; ring -- Norm f norm_smul issue
    apply (hG.add ht (Wallet.sum ht hv)).of_est; filter_upwards [hu.pos] with i hi
    have he: bands D' n ⊆ bands D' (n+1):= fun x hx=> (full_bands ..).2 (((full_bands ..).1 hx).trans n.le_succ); let H:= U.α.unselected.algebra;
    have hh : g! i=G i+∑ x∈ V,z₀ x i:=by
       -- notation g! quotes fun not parenthesized
       unfold groundError G; rw [show groundError U P (n+1) (x i) p (z i) (y i) q = _ from rfl]; change _= (viewing U _ _-∑ w∈bands D' _,z₀ w i)+ _; rw [← Finset.sum_sdiff he]; unfold V z₀; abel
    rw [Real.norm_of_nonneg (mul_nonneg hi.le (norm_nonneg _))]; change Y i* ‖g! i‖ ≤ Y i * ‖G i‖+ _; rw [hh,← Finset.mul_sum,← mul_add]; exact mul_le_mul_of_nonneg_left ((norm_add_le (G i) (∑ w∈V,z₀ w i)).trans (add_le_add_right (norm_sum_le V (fun w=>z₀ w i)) _)) hi.le
end YM.OPE.Log
