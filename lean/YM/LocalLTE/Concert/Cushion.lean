import YM.LocalLTE.Concert.Packet
/-!
# Numerical reading of CONDITIONAL LOG/value, in the physical theory. On all passing V (incl flagged not all? only those with *no flags* for this corollary*. Always keep global densities with actual gas).

Intrinsic statement is supported norm. Here reduce to output value prices for source probes (no cheap extensive/corner reading without this step).
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Port
open Function Filter Set Lattice Wilson RG Overlay Marker Finset MeasureTheory
open Work.H03 Extra.Trajectories Progress.DirectedRecipe Layers Push.AbsoluteSums
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{n:Side} {P:Rep G n}
variable {V:Type}[DecidableEq V][Fintype V] {R:Census V} (A B D:Overlay.Bands R P)(t:V→ℝ)
variable (U:Config G n) {a b c d e f A' B' x y s:ℝ}
local notation "pv"=> Poly.price t
open Overlay
lemma tones {F:Overlay.Bands R P}(h:F.Active)(hw:F.Radial t a b c d): (F.extra U).part R.quiet=0:=by
    let T:= F.bulkBound h hw U
    have hh (i : R.Mode) (hx : i.val.Nonempty) (x : ℂ) : (Poly.send i x).part R.quiet=0 := by rw [Poly.part_send,if_neg (show R.quiet≠i from fun H => nonempty_iff_ne_empty.mp hx (congr_arg Subtype.val H.symm))]
    rw [Bands.extra,Poly.part_plus,Poly.share T.1,Poly.part_sum]; simp_rw [Bands.ray, hh _ (h.proper _),hh _ (show (R.fire _).val.Nonempty from Finset.singleton_nonempty _), tsum_zero,sum_const_zero,zero_add]
-- harmonic bounds
lemma extraEqual (hb:B.Active)(hD:D.Active)(hB:B.Radial t a B' x d)(hp:D.Radial t 0 e f d)(hq: Fan.Tabs P R A B D): A.extra U= B.extra U+D.extra U:=by
    have H i:A.ray i U=B.ray i U+D.ray i U :=by
       unfold Bands.ray; have he:A.H i= B.H i+D.H i:= by rw [← hq.hess]; change A.H i=B.H i+(A.H i-B.H i); abel
       have ht:=hq.outer; have hu:=hq.reach; have hy:=hq.index; rw [← ht,← hu,← hy, ← hq.bits,he]; by_cases hf: Healthy P.p.threshold (A.support i) U
       · rw [masked_eq _ _ _ _ hf,masked_eq _ _ _ _ hf,masked_eq _ _ _ _ hf]; ext u; simp only [Poly.part_plus, Poly.part_send,Pi.add_apply]; split <;> ring
       rw [masked_ne _ _ _ _ hf,masked_ne _ _ _ _ hf,masked_ne _ _ _ _ hf];simp
    have hV: (∑' i,A.ray i U)= (∑' i,B.ray i U)+(∑' i,D.ray i U):=calc
        _=∑' i, (B.ray i U+D.ray i U) := tsum_congr H
        _ =_:= Summable.tsum_add (B.bulkBound hb hB U|>.1) (D.bulkBound hD hp U|>.1)
    unfold Bands.extra; rw [hV,hq.battens,hq.units]; simp only [Pi.zero_apply, Poly.send_zero, sum_const_zero,zero_add,add_assoc]
-- some unused ha/h.U.instructions remove. pass_smallC explicit const.Power.
local notation "M"=> Fintype.card V
lemma outbound (hw:∀ i,0<t i) (b:Poly R){k:ℕ} (hk:Fintype.card V ≤ k) {θ:ℝ} (hv:pv b ≤ (k:ℝ)*θ) (hu:0 ≤ θ) (he: θ ≤ 1): pv (Poly.pass b-1) ≤ (∑ i∈ Finset.range (k+1), ‖((i.factorial:ℂ)⁻¹)‖*(k:ℝ)^i)*θ:=by
    let B:= Finset.range (Fintype.card V+1); let C:= Finset.range (k+1)
    have hx:0∈B:= mem_range.mpr (by omega); let f (i:ℕ):Poly R:= ((i.factorial:ℂ)⁻¹) • b^i
    have ht: Poly.pass b-1= ∑ i∈B.erase 0,f i:=by rw [Poly.pass,← Finset.sum_erase_add B _ hx]; simp; rfl -- reducible
    rw [ht]; apply (Poly.batch hw _ _).trans; let w(i:ℕ):= ‖((i.factorial:ℂ)⁻¹)‖*(k:ℝ)^i*θ
    rw [sum_mul]; refine (sum_le_sum (g:=w) ?_).trans (sum_le_sum_of_subset_of_nonneg (show B.erase 0⊆ C from (erase_subset ..).trans (range_mono (by omega))) fun i _ _=>?_) -- need edits
    · intro i hi; unfold f; rw [Poly.adapted]; unfold w; rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply le_trans (Poly.powers hw b i) ((pow_le_pow_left₀ (Poly.nonnegative hw _) hv i).trans (?_)); rw [mul_pow]; apply mul_le_mul_of_nonneg_left _ (by positivity); have hg:=pow_le_pow_of_le_one hu he (show 1 ≤ i from Nat.one_le_iff_ne_zero.mpr (mem_erase.mp hi).1); rwa [pow_one] at hg
    unfold w; positivity
lemma hymn (hb:B.Active)(hD:D.Active) (hB:B.Radial t a B' x d)(hp:D.Radial t 0 e f d)(hc:0 ≤ e)(hx:e≤1) (hq:Fan.Tabs P R A B D)
    (z:ℝ)(H1:(a+B') ≤ z) (hz:0≤z) (k:ℕ) (hr:Fintype.card V ≤ k): pv (A.extra U - B.extra U) ≤ (k:ℝ)*e ∧ pv (Poly.pass (A.extra U)-Poly.pass (B.extra U)) ≤ (Real.exp ((k:ℝ)*z)*(∑ i∈Finset.range (k+1),‖((i.factorial:ℂ)⁻¹)‖*(k:ℝ)^i))*e :=by
    have he:=Extra.Trajectories.pass_add (tones t U hb hB) (tones t U hD hp); have ha:= Port.extraEqual A B D t U hb hD hB hp hq
    have hφ:=D.bulkBound hD hp U|>.2; rw [zero_add] at hφ; replace hr':(Fintype.card V:ℝ) ≤ k:=by exact_mod_cast hr
    have hh:=hφ.trans (mul_le_mul_of_nonneg_right hr' hc); have hg (i:Poly R): i*Poly.pass (D.extra U)-i=i*(Poly.pass (D.extra U)-1):=by ring
    have ht:pv (Poly.pass (B.extra U)) ≤ Real.exp ((k:ℝ)*z):=by refine (Poly.pass_budget hB.pure _).trans (Real.exp_monotone ((B.bulkBound hb hB U).2.trans ((mul_le_mul_of_nonneg_left H1 (Nat.cast_nonneg _)).trans (mul_le_mul_of_nonneg_right hr' hz)))) -- mul args wrong
    rw [ha,add_sub_cancel_left, he, hg]; refine ⟨hh,?_⟩
    apply (Poly.multiplication hB.pure _ _).trans; rw [mul_assoc]; exact mul_le_mul ht (outbound t hB.pure _ hr hh hc hx) (Poly.nonnegative hB.pure _) (Real.exp_nonneg _)
lemma beacon (P:Poly R)(x t σ:ℝ) (K:ℕ)(hx:1≤x)(ht:0 ≤t)(hs:Fintype.card V ≤ K) {E r ζ:ℝ} (he:σ≥0)(hp:Poly.price (fun _=> PhysicalNext.Repeat.Mallow.neat x t) P ≤ σ*x^(-E)) (hL:(t+2)*K+(-E)≤ -ζ)(h: x^(-ζ)≤ r): Poly.price (fun _=>1) P ≤ σ*r:=by
    let u:V→ℝ:=fun _=> PhysicalNext.Repeat.Mallow.neat x t; let κ:= x^(t+2); let k:=κ^K; have ho:1 ≤κ:= Real.one_le_rpow hx (by positivity); have h0:0 ≤ k:=pow_nonneg (zero_le_one.trans ho) _
    have hα (i:R.Mode):Poly.toll (fun _=> (1:ℝ)) i ≤ k*Poly.toll u i:=by
       have hf(i): (1:ℝ) ≤ κ*u i:= le_of_eq (by unfold u κ PhysicalNext.Repeat.Mallow.neat; rw [← Real.rpow_add (by positivity),show t+2+(-t-2)=0 by abel, Real.rpow_zero]) -- unfold
       apply le_trans (prod_le_prod (s:=i.val) (fun _ _=>zero_le_one) (fun i _=>hf i)) _; rw [prod_mul_distrib,prod_const]; exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ ho ((card_le_univ _).trans hs)) (Poly.worth (fun _=>Real.rpow_pos_of_pos (zero_lt_one.trans_le hx) _) _).le -- check order.
    apply le_trans (b:=k*Poly.price u P) _ ((mul_le_mul_of_nonneg_left hp h0).trans _)
    · unfold Poly.price; rw [mul_sum]; refine sum_le_sum fun i _=>?_; rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right (hα i) (norm_nonneg _)
    rw [mul_left_comm k σ]; apply mul_le_mul_of_nonneg_left _ he; unfold k κ; rw [← Real.rpow_mul_natCast (by positivity), ← Real.rpow_add (by positivity)]; exact le_trans (Real.rpow_le_rpow_of_exponent_le hx hL) h
end YM.LocalLTE.Port
