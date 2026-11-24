import YangMills.WilsonProof.NativeSupport.Commissioned259.ScaleCost.Complete
/-!
# The compact (G.1) purchase on the thermometer & home reads, *including positive and
negative* η. Use with `movement` / `budget` for growing hypothesis part of G.1.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.ScaleCost
open Filter Function Set Asymptotics Comparing Matrix PowerSeries
open MS.Book.Program XSpace XSpace.Normalize O.Score O.Enh Dframe FVA2.Scale Quotes
open scoped Topology BigOperators Classical
variable {G : Gauge} {V : Arenas G} {R : ℝ→PowerSeries ℂ} {B : ℝ→Frames G} (H : Law V R B)
variable {W W' : ℝ} {I : Type*} {X : Filter I} {T r : I→ℝ}
local notation "late" => 𝓝[>] (0:ℝ)
variable (hG : G.Simple) {t : ℝ→ℝ} (ht : t=O[late] (g0 G)) {D : Route G} (hD : Balances D) (h' : selfCharge D) (P : StepCost G R B t D)
    (hr : Tendsto r X late) (hT : ∀ᶠ i in X,T i ∈ Icc 1 W) (hB : ∀ᶠ i in X,T i ∈ Icc W 1)
    {d p : ℕ}
local notation "g" => g0 G
local notation "s" => (fun i:I=>r i*T i)
local notation "α" => t∘r
local notation "bill" => paired D B R t p d
include hG H ht hD h' P
-- already possible p=0 for higher motion [1,W] by `chunk`.
include hr
include hT in
omit h' in
lemma classic_upper : (fun i=> bill (r i) (T i))=O[X] fun i=> g0 G (r i)^(p+1) := by
  obtain ⟨M,h⟩:= chunk H hG ht hD P hr hT p d
  exact (isBigO_norm_left.mpr ((local_cash h.expense).congr_right fun _=>mul_one _)).add (matrixPay.mpr fun i j=> (local_cash (M i j).expense).congr_right fun _=>mul_one _)
variable (hp:0<p) (hm:0<W)
include hp hB hm
lemma classic_lower : (fun i=> bill (r i) (T i))=O[X] fun i=> g0 G (r i)^(p+1) := by
  let F:=fun i:I=>(T i)⁻¹; let s':I→ℝ:= s
  have v : ∀ᶠ i in X, 0< T i := hB.mono fun i h=> hm.trans_le h.1
  have y : ∀ᶠ i in X, F i∈Icc 1 W⁻¹ := hB.mono fun i h=>⟨ (one_le_inv₀ (hm.trans_le h.1)).mpr h.2, inv_anti₀ hm h.1⟩
  have e : Tendsto s' X late := Comparing.hull (a:=1) (b:=0) hG v hr (by simpa using (hB.mono fun i h=>h.2))
  obtain ⟨M,C⟩:= compact_opposed H hG ht hD h' P e y p hp (d:=d)
  refine (IsBigO.add (isBigO_norm_left.mpr C) M).congr' ?_ ?_
  · have w (T t:ℝ) : form B d T p t=columns (accepts (conversion B (-Real.log T) d) p t) := by
      apply Matrix.ext; intro i j; exact Eq.symm (fee_matrix _ i j p t)
    filter_upwards [v] with i hi; unfold s' F; dsimp only [paired,Function.comp]
    -- rewrite (s i * F i = r i)
    rw [mul_assoc _ (T i) _, mul_inv_cancel₀ hi.ne',mul_one,Real.log_inv, w]
  filter_upwards [v] with i hi; unfold s' F; rw [mul_assoc _ (T i) _, mul_inv_cancel₀ hi.ne',mul_one]
omit hB hr
lemma compact_cost (W':ℝ) : ∃ C:ℝ,0<C ∧ ∀ᶠ r in late, ∀ T ∈ Icc W W',
    paired D B R t p d r T ≤ C*g0 G r^(p+1) := by
  let X1(a b:ℝ):=ℝ×↥(Icc a b); let F(a b:ℝ):Filter (X1 a b):= comap Prod.fst late
  have h (a b:ℝ): ∀ᶠ i in F a b,i.2.val∈ Icc a b := Eventually.of_forall fun i=> i.2.property
  have E(a b:ℝ)(h:(fun i:X1 a b=> paired D B R t p d i.1 i.2.val)=O[F a b] fun i=>g i.1^(p+1)) : ∃ C:ℝ,0<C ∧ ∀ᶠ r in late,∀ T∈Icc a b, bill r T≤ C*g r^(p+1) := by
    obtain ⟨C,hC,E⟩:= h.exists_pos; refine ⟨C,hC,?_⟩; filter_upwards [eventually_comap.mp E.bound, g0_pos hG] with i z p' T h'; have u:= z ((i,⟨T,h'⟩):X1 a b) rfl; change ‖bill i T‖≤ C* ‖g0 G i ^ (p+1)‖ at u; exact (le_abs_self _).trans (u.trans_eq (by rw [Real.norm_of_nonneg (pow_nonneg p'.le _)]))
  obtain ⟨A,hA,H1⟩:= E 1 W' (classic_upper H hG ht hD P tendsto_comap (h 1 W')); obtain ⟨B',hB',H2⟩:= E W 1 (classic_lower H hG ht hD h' P tendsto_comap (h W 1) hp hm)
  refine ⟨max A B',lt_max_of_lt_left hA,?_⟩; filter_upwards [H1,H2,g0_pos hG] with i H K u T hT
  rcases le_total 1 T with h|h
  · exact (H _ ⟨h,hT.2⟩).trans (mul_le_mul_of_nonneg_right (le_max_left ..) (pow_nonneg u.le _))
  exact (K _ ⟨hT.1,h⟩).trans (mul_le_mul_of_nonneg_right (le_max_right ..) (pow_nonneg u.le _))
omit hm
lemma classic (S:Set ℝ)(hs:IsCompact S) : ∃ C:ℝ,0<C ∧ ∀ᶠ r in late, ∀ η ∈ S,
    (let s' := r*Real.exp (-η); let Ψ:= R η; let A:=D r s' d; let Z:=conversion B η d
     ‖(↑(t s'):ℂ)-crop p (t r) Ψ‖ + stiffness (columns A-columns (accepts Z p (t r))) ≤ C*g r^(p+1)) := by
  obtain ⟨M,hM⟩:= hs.bddBelow; obtain ⟨L,hL⟩:= hs.bddAbove
  obtain ⟨C,hC,E⟩:= compact_cost H hG ht hD h' P (d:=d) hp (Real.exp_pos (-L)) (Real.exp (-M)); refine ⟨C,hC,?_⟩
  filter_upwards [E] with r H i hi s' Ψ A Z
  specialize H (Real.exp (-i)) ⟨Real.exp_le_exp.mpr (neg_le_neg (hL hi)), Real.exp_le_exp.mpr (neg_le_neg (hM hi))⟩; unfold paired at H; rw [show form B d (Real.exp (-i)) p (t r)=_ from ?_,Real.log_exp,neg_neg] at H; exact H
  change form B d (Real.exp (-i)) p (t r)=columns (accepts (conversion B i d) p (t r))
  apply Matrix.ext; intro i j; unfold form; rw [Real.log_exp,neg_neg]; exact Eq.symm (fee_matrix _ i j p (t r))
end YM.FVA2.GradedFar259.ScaleCost
