import YM.MatchingLedger.Periodical.Monthly

/-!
# Pointwise restore all shell/boundary contributions needed by one-step SD

Undo shutter, keeping actual-dependent fine/log words. The all-sector polynomial bound outside
is deliberately weak, so the bad-occurrence probability has to beat this UNweighted loss
(including angles not tiny). Use full physical pressure.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MatchingLedger.Periodical
open Function Filter Lattice RG Wilson Tree Pressure Pressure.Stores Precision Push.Uniform
open PatchArea Action Books MvPolynomial Gazette Set Metric
open MeasureTheory
open scoped Topology Classical BigOperators Matrix.Norms.Frobenius ContDiff Finset
variable {c f : Side}{G : Gauge}{S : StepData c f} (F : Forest S.ratio) (s : S.Choices) (hB:S.patch.Branches S.kernel G)
    {A : ChartRatio G} (Y : Chip (Page G c)) {t Z : ℝ} (i : Needle F G)(k d : ℕ) (H : Budget G A (d+3))

local notation "a" => (t⁻¹*Z)
local notation "ι" => Needle F G
local notation "I" => Sum.inl i
local notation "D" => depot F (Sum.inl i)
local notation "V" => edition F s A Y
local notation "M" => H.income S.patch S.kernel

section general
-- `R` support includes any needed query plus all SD poles used. lead mask inherited
-- via higher prices; grade 0 special.
def readings (A : ChartRatio G) (t : ℝ) : Poly (Needle F G) := install Y (lead F s i k A t⁻¹)
lemma current_entry (t : ℝ) : readings F s Y i k A t=∑ j∈Finset.range (k+1), (t⁻¹ : ℝ)^j • (pderiv i (V j)):= by
  unfold readings lead; simp_rw [_root_.map_sum,_root_.map_smul, ← install_gradient]; rfl
lemma range_pderiv {α : Type}(v : ℕ→Poly α)(i:α) (k:ℕ) (t : ℝ) : (∑ j∈ Finset.range (k+1), t^j • pderiv i (v j))= FPS.base v i + ∑ j∈Finset.range (k+1), (t : ℝ)^j • (FPS.slope v i j):= by
  unfold FPS.base; rw [ Finset.sum_range_succ', Finset.sum_range_succ' (fun j : ℕ=> t^j • FPS.slope v i j)]; simp only [FPS.slope,FPS.higher,pow_zero,one_smul,_root_.map_zero,add_zero]; exact add_comm ..

lemma current_paid (t : ℝ) : readings F s Y i k A t=FPS.base V i + ∑ j∈Finset.range (k+1), (t⁻¹ : ℝ)^j • (FPS.slope V i j):= by
  rw [current_entry]; exact range_pderiv V i k t⁻¹

def notice (p : Poly ι)(A : ChartRatio G)(t : ℝ) := readings F s Y i k A t * p- pderiv i p
lemma merge_notice (p:Poly ι) (L:Prediction ι) (t : ℝ): L (notice F s Y i k p A t) = Books.FPS.ley V i (fun _=> L) p t⁻¹ k:= by
  unfold notice; rw [current_paid,FPS.dynamic_test]; congr 1
  rw [add_mul,Finset.sum_mul]; unfold FPS.force
  simp_rw [smul_mul_assoc]; ring

variable (ht:1≤t)(hZ:1≤Z)(hY:‖Y‖≤ Z)
variable {R : Support c}
    (hr : t⁻¹*Z≤dial A) (hh:t⁻¹*Z ≤ H.space S.patch S.kernel)
    (hR:arc F (.inl i)⊆ R) (he:k≤d)
    (p : Token (Needle F G)) (hm : p.support ⊆ located (nest F) R) (hd : heft p≤d)

include hZ hY hB in
private lemma origin_owned : Value F i (pderiv i (V 0)) 1 (gradientBill G S.patch M 2 * Z) := by
  have he := Ticket F H Y i (tip_paid F s H hB H.nn (.inl i)) hZ hY
  have hu : pderiv i (V 0) = pderiv i (install Y (tip F s 2)):= rfl
  rw [hu]; simpa only [show 2-1=1 from rfl, pow_one] using he

include H hZ hY hB in
lemma read_ports (hf : k≤d) : ∀ j∈(readings F s Y i k A t).vars, nest F j∈arc F I := by
  rw [current_entry]; intro j hj; obtain ⟨u,hu,h⟩:= Finset.mem_biUnion.mp (vars_sum_subset _ _ hj)
  have hu := Finset.mem_range.mp hu
  have hm : j∈ (pderiv i (V u)).vars:=by
    rw [Algebra.smul_def] at h
    have hv:= vars_mul _ _ h; exact (Finset.mem_union.mp hv).resolve_left (by simp)
  change atlas F (.inl j)∈_; refine (loc («a»:=atlas F)).mp ?_
  by_cases ho:u=0
  · subst u; exact (origin_owned F s hB Y i d H hZ hY).port j hm -- arg order
  have he := slope_ticket F s hB Y H (show u+2≤d+3 from by omega) i (Nat.pos_of_ne_zero ho) Z hZ hY
  apply he.port; cases u; exact False.elim (ho rfl); exact hm

include H hZ hY hR he hB ht in
lemma reload (U:F.Slice G) : (run F A t (readings F s Y i k A t)) U = read (t • column F A (t⁻¹ • Y) R U) (lead F s i k A t⁻¹):= by
  unfold run
  let q:= readings F s Y i k A t; let y:= stage F A R U
  have hb : t≠0:=(zero_lt_one.trans_le ht).ne'
  have hv : read (t • crawl F A U) q = read (t • y) q:= read_only fun j hj=> by
    have hx := hR (read_ports F s hB Y i k d H hZ hY he _ hj); change t * _= t*stage F A R U j; rw [onstage, if_pos hx]
  rw [hv]; unfold q readings; rw [install_read]; congr 2; unfold column; ext j; cases j; rfl
  rename_i j; change _= t*(t⁻¹ * Y j); rw [mul_inv_cancel_left₀ hb]; rfl

local notation "ξ" => fieldTest (G:=G) F R
local notation "P" => notice F s Y i k (mark p) A t
local notation "E" => milled F s A (t⁻¹ • Y) t a R i (mark p)
local notation "J" => run F A t P

-- near χ=1 on strict smaller ball; in all cases on gate we will use conservative global bounds
include hR hr ht hZ in
lemma still_cool {U:F.Slice G} (hf:U∈ ξ (a/4)): scatter F A a i U=1 ∧ arrow F A a i U=0:=by
  have hg:0<t⁻¹:= inv_pos.mpr (zero_lt_one.trans_le ht); have hp : 0 < Z:=zero_lt_one.trans_le hZ; have hw : (t⁻¹*Z)/4≤ a:=by apply div_le_self (by positivity) (by norm_num)
  have hu:= cut_one (mul_pos hg hp) (pedal (hw.trans hr) (hf i.1 (has_address F i R hR))).1
  refine ⟨hu.eq_of_nhds,?_⟩; unfold arrow; rw [hu.fderiv_eq]; simp

-- fixed-order pitch
-- assumes hY, no small mesh price hidden
include hh ht hr hY hZ he hR hB
lemma ordered {U : F.Slice G} (hf:U∈ξ a) :
    ‖t⁻¹ * distill F s A t i (column F A (t⁻¹ • Y) R U) - run F A t (readings F s Y i k A t) U‖ ≤
      park (belt S.patch) * (2*M*Z^(k+2))*(t⁻¹)^(k+1):=by
   let Y':= t⁻¹ • Y; let L:=column F A Y' R U
   have hp: 0<t:= zero_lt_one.trans_le ht; have hv:‖L‖≤ a:= column_range F Y' hr (by unfold Y'; rw [norm_smul_of_nonneg]; exact mul_le_mul_of_nonneg_left hY (by positivity); positivity) hf
   let X:=t • L; have hX: t⁻¹ • X=L:=by simp [X, smul_smul, hp.ne']
   rw [reload F s hB Y i k d H ht hZ hY hR he]; apply le_trans (b:=‖_*_ - _‖) (le_of_eq ?_) (ruling F s hB i k H X hp (by rw [hX]; exact hv.trans hh) (by omega) Z hZ (by unfold X; rw [norm_smul_of_nonneg hp.le]; exact (mul_le_mul_of_nonneg_left hv hp.le).trans_eq (mul_inv_cancel_left₀ hp.ne' _))) -- use simpa
   rw [hX]

include hm hd in
omit hY he hR hB hh in
lemma word_le {U:F.Slice G} (hf:U∈ξ a) : ‖run F A t (mark p) U‖≤ Z^d:= by
  have ht':0<t:=zero_lt_one.trans_le ht
  refine (read_term p _ (zero_le_one.trans hZ) (fun j hj=>?_)).trans (pow_le_pow_right₀ hZ hd); rw [Pi.smul_apply,norm_smul_of_nonneg ht'.le]; exact (mul_le_mul_of_nonneg_left (color_inside F hr hf j (loc.mp (hm hj))) ht'.le).trans_eq (mul_inv_cancel_left₀ ht'.ne' _)

include hd in
lemma quiet {U:F.Slice G} (hf:U∈ ξ (a/4)) (hm' : p.support⊆located (nest F) R) :
    ‖J U - E U‖ ≤ (Z^d) * (park (belt S.patch) * (2*M*Z^(k+2)))*(t⁻¹)^(k+1) := by
   have hp:0<t:= zero_lt_one.trans_le ht; have hZ':0<Z:= zero_lt_one.trans_le hZ
   have hU: U∈ξ a := inside_cov F G (by apply div_le_self (by positivity) (by norm_num) : a/4≤a) hf
   obtain ⟨hw,hq⟩:= still_cool F i ht hZ hr hR hf
   rw [milled, indicator_of_mem hU, radix,hw,hq]
   let X:= t⁻¹*distill F s A t i (column F A (t⁻¹ • Y) R U); let Q:=run F A t (readings F s Y i k A t) U; let u:= run F A t (mark p) U
   have hv: J U= Q*u-run F A t (pderiv i (mark p)) U:= by unfold run Q u notice; rw [_root_.map_sub,read_mul]; rfl
   rw [hv]; change ‖Q*u-_ - (1*(u*X-_)-_*0*u)‖≤ _; rw [show Q*u-run F A t (pderiv i (mark p)) U - (_) = -(u*(X-Q)) by ring,norm_neg,norm_mul]; rw [mul_assoc (Z^d)]; exact mul_le_mul (word_le F d ht hZ hr p hm' hd hU) (ordered F s hB Y i k d H ht hZ hY hr hh hR he hU) (norm_nonneg _) (pow_nonneg (zero_le_one.trans hZ) _)

end general
end YM.MatchingLedger.Periodical
