import YM.Comparison.RG02.Order.Eval

/-!
# Marked denominator costs, without using a finite-dimensional norm equivalence

A reader for the analytic & localization statements to come. Work at *one step* with a
full marked push and the same vacuum component. `unitScale` can be applied after multiplying
the entire table by a common scalar (the fixed factor from the integral formulas; apply also
with volume factors for a virtual-period proof). Never apply independently to the numerator
markers. Keep the denominator lower bounds or relative estimates explicit -- algebra alone gives
no useful uniform-in-volume reciprocal bound.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Order
open Finset Function YM.Marker YM.Multi Join YM.Primitives.GCC.Anchor
open YM.Extra.Trajectories (connected connected_quiet pass_connected part_sub)
open YM.Comparison.RG02.Cumulants
open scoped BigOperators Classical
variable {V : Type} [DecidableEq V] [Fintype V] {R : Census V} {r : ℕ}

/-- Normalize a table with nonzero quiet part (use after proving it is nonzero).
    Same table used for all physical insertions. -/
def unitScale (x : Poly R) := (x.part R.quiet)⁻¹ • x
omit [Fintype V] in lemma unitScore {x : Poly R} (h : x.part R.quiet ≠ 0) :
    (unitScale x).part R.quiet=1 := inv_mul_cancel₀ h
omit [Fintype V] in lemma scale_value {x : Poly R} (h : x.part R.quiet ≠ 0) :
    x.part R.quiet • unitScale x=x := by rw [unitScale, smul_smul, mul_inv_cancel₀ h, one_smul]
omit [Fintype V] in lemma scaled_same (x : Poly R) (z : ℂ) (h : z ≠ 0) :
    unitScale (z•x)=unitScale x := by
  unfold unitScale; rw [Poly.part_smul,mul_inv_rev,smul_smul,mul_assoc, inv_mul_cancel₀ h,mul_one]
omit [Fintype V] in lemma scaled_reconstruct {x : Poly R} (h : x.part R.quiet ≠ 0) (q : Poly R) :
    x-x.part R.quiet • q=x.part R.quiet • (unitScale x-q) := by rw [smul_sub,scale_value h]

-- relative (inside price operations, keep cancellation at the union of actual normalized entries)
omit [Fintype V] in lemma priced_neg (w : V→ℝ) (x : Poly R) : Poly.price w (-x)=Poly.price w x := by
  rw [← neg_one_smul ℂ x, Poly.adapted]; simp
omit [Fintype V] in lemma priced_sub (w : V→ℝ) (hw : ∀ i,0<w i) (x y : Poly R) :
    Poly.price w (x-y) ≤ Poly.price w x+Poly.price w y := ( (sub_eq_add_neg x y).symm ▸ Poly.addition hw x (-y)).trans_eq (by rw [priced_neg])
omit [Fintype V] in lemma scale_price {x : Poly R} (h : x.part R.quiet ≠ 0) (w : V→ℝ) (hw : ∀ i,0<w i)
    {b : ℝ} (he : b ≤ ‖x.part R.quiet‖) (q : Poly R) :
    b*Poly.price w (unitScale x-q) ≤ Poly.price w (x-x.part R.quiet • q) := by
  rw [scaled_reconstruct h,Poly.adapted]; exact mul_le_mul_of_nonneg_right he (Poly.nonnegative hw _)

lemma leading_trunc_value {x : Grade R r} (h : bottom R r x=1) (g : ℂ) :
    (value g x).part R.quiet=1 := by
  have hx : denominator x=1 := h
  have he : value g (1 : Grade R r)=1 := by rw [← map_one (series R r),← short_value,PowerSeries.trunc_one,map_one]
  have hi := (value_denom x g).symm.trans (by rw [hx,he])
  simpa using congrArg (Poly.part · R.quiet) (show Poly.send R.quiet _=1 from hi)

/-- Exact difference before division, against a full table whose vacuum is not 1. `E` is the
 numerical remainder compared to `value g x` (with the same leading scale before all these
 operations). Keep it signed and the same quiet component in both uses. Do not replace this
 identity by a triangle estimate if the analytic test needs cancellation. -/
lemma ratio_defect {x : Grade R r} (h : UnitLeading x) (hx : Symmetric x) (g : ℂ)
    (F E : Poly R) (he : F=value g x+E) :
    F-F.part R.quiet • value g (ratio x)=E-E.part R.quiet • value g (ratio x) -
      omitted r g (render (denominator x) * render (ratio x)) := by

  have ht := value_multiply (denominator x) (ratio x) hx.vacant (sym_ratio h hx) g
  rw [value_denom, recovers h, Poly.product_bead] at ht
  rw [he,Poly.part_plus,add_smul, ht]; abel

/-- Conditional consumer explicit. This is often a **finite or auxiliary** volume estimate;
    in large volume retain the preceding identity with relative estimates on the log operations,
    don't assert that extensive `‖F-vac Taylor‖` is small. -/
theorem ratio_pay {x : Grade R r} (h : UnitLeading x) (hx : Symmetric x) (g : ℂ) {z : ℝ} (hz : ‖g‖≤z)
    (F E : Poly R) (hF : F.part R.quiet ≠ 0) (he : F=value g x+E) {b : ℝ} (hb : b≤ ‖F.part R.quiet‖)
    (w : V→ℝ) (hw : ∀ i,0<w i) :
    b * Poly.price w (unitScale F - value g (ratio x)) ≤
    Poly.price w (E-E.part R.quiet • value g (ratio x)) + ‖g‖^(r+1) *
      subtotal w r z (render (denominator x) * render (ratio x)) := by
  refine (scale_price hF w hw hb _).trans ?_
  rw [ratio_defect h hx g F E he]; exact (priced_sub w hw ..).trans (add_le_add le_rfl (tail_bound w hw r z _ g hz))

section TruncLog
omit [Fintype V] in lemma ends {x : Poly R} {b n : ℕ} (h : x.part R.quiet=0) (hx : ∀ t:R.Mode,t.val.card≤b) (hb : b < n) :
    x^n=0 := Poly.ext fun v=>Poly.high _ h _ _ ((lt_of_le_of_lt (hx v) hb))
lemma room_for (b : ℕ) (h : ∀ s:R.Mode,s.val.card≤b) (p : (Board R r).Mode) : p.val.card≤b+r := by
  rw [← card_toLeft_add_card_toRight]; exact add_le_add (h (left p)) (order_limit r (right p))
def logTo (n : ℕ) (p : Poly R) := ∑ i∈range n, (-((↑(i+1) : ℂ))⁻¹) • (1-p)^(i+1)
omit [Fintype V] in
private lemma extends_log (p : Poly R) (hp : p.part R.quiet=1) {m n : ℕ} (hb : m≤n)
    (h : ∀ t : R.Mode, t.val.card≤m) : logTo m p=logTo n p := by
  apply Finset.sum_subset (Finset.range_mono hb); intro k _ hk
  rw [ends (show (1-p).part R.quiet=0 from by simp [part_sub,hp]) h (by simp only [mem_range, not_lt] at hk; omega),smul_zero]
lemma log_to (x : Poly R) (hp : x.part R.quiet=1) (m : ℕ) (hm : ∀ t:R.Mode,t.val.card≤m) :
    connected x=logTo m x := by
  rw [log_formula hp]; let s:= Fintype.card V + 1
  exact (extends_log x hp (le_max_left s m) (fun t=>(card_le_univ _).trans (Nat.le_succ _))).trans
    (extends_log x hp (le_max_right s m) hm).symm

def logSeries (n : ℕ) (p : Truncated R) : Truncated R := ∑ i∈range n,
    Polynomial.C (algebraMap ℂ (Poly R) (-((↑(i+1) : ℂ))⁻¹)) * (1-p)^(i+1)
lemma stamp_log (n : ℕ) (p : Truncated R) :
    stamp R r (logSeries n p)=logTo n (stamp R r p) := by
  simp only [logSeries, map_sum, stamp_scalar,map_pow,map_sub,map_one,logTo]
omit [Fintype V] in
lemma formula_log (g : ℂ) (n : ℕ) (p : Truncated R) :
    formula g (logSeries n p)=logTo n (formula g p) := by
  simp_rw [logSeries,map_sum,map_mul,map_pow,formula_const,logTo,map_sub,map_one, Algebra.smul_def]

theorem log_mark_defect {x : Grade R r} (h : UnitLeading x) (hx : Symmetric x) (g : ℂ)
    (a : ℕ) (ha : ∀ t:R.Mode,t.val.card≤a) :
    connected (value g (ratio x)) = value g (logMarked x) +
      omitted r g (logSeries (a+r) (render (ratio x))) := by
  have h' := leading_trunc_value (ratio_pure h) g
  rw [logMarked, log_to (ratio x) (ratio_quiet h) (a+r) (room_for a ha), log_to _ h' (a+r)
    (fun t=> (ha t).trans (Nat.le_add_right ..)),value_render g (ratio x),← formula_log,
    formula_omits r _ g, stamp_log,rerender (sym_ratio h hx)]

end TruncLog

section Lipschitz
omit [Fintype V] in
lemma power_price (p q : Poly R) (w : V→ℝ) (hw : ∀ i,0<w i) {M : ℝ}
    (hp : Poly.price w p ≤ M) (hq : Poly.price w q ≤ M) (i : ℕ) :
    Poly.price w (p^(i+1)-q^(i+1)) ≤ (i+1:ℕ)*M^i*Poly.price w (p-q) := by
  have h := (Poly.nonnegative hw p).trans hp; let a:= Poly.price w (p-q)
  have hl := Poly.nonnegative hw (p-q)
  induction i with
  | zero => simp
  | succ i IH =>
    rw [show p^(i+1+1)-q^(i+1+1)=p*(p^(i+1)-q^(i+1)) + q^(i+1)*(p-q) by ring]
    refine (Poly.addition hw ..).trans <| (add_le_add (Poly.multiplication hw ..) (Poly.multiplication hw ..)).trans ?_
    apply le_trans (b:=M*((i+1:ℕ)*M^i*a)+M^(i+1)*a)
    · apply add_le_add (mul_le_mul hp IH (Poly.nonnegative hw _) h) (mul_le_mul_of_nonneg_right (le_trans
        (Poly.powers hw _ _) (pow_le_pow_left₀ (Poly.nonnegative hw _) hq _)) hl)
    exact Eq.le (by unfold a; push_cast; ring)

def repeats (d : ℕ) (M : ℝ) := ∑ i∈range d,M^i
lemma repeats_pos (d : ℕ) (M : ℝ) (hM : 0≤M) : 0 ≤ repeats d M := sum_nonneg fun i _=> pow_nonneg hM i
lemma lip (x y : Poly R) (w : V→ℝ) (hw : ∀ i,0<w i) {M : ℝ}
    (hx : x.part R.quiet=1) (hy : y.part R.quiet=1)
    (hX : Poly.price w (1-x) ≤ M) (hY : Poly.price w (1-y) ≤ M)
    (d : ℕ) (hd : ∀ t:R.Mode,t.val.card≤d) :
    Poly.price w (connected x-connected y) ≤ repeats d M * Poly.price w (x-y) := by
  rw [log_to x hx d hd, log_to y hy d hd]; unfold logTo repeats
  rw [← Finset.sum_sub_distrib]
  refine (Poly.batch hw ..).trans ?_; rw [Finset.sum_mul]; refine sum_le_sum fun i _=> ?_
  have ht := power_price _ _ w hw hX hY i
  rw [sub_sub_sub_cancel_left,← neg_sub x y, priced_neg] at ht
  rw [← smul_sub, Poly.adapted, norm_neg,norm_inv]
  have hz : ‖(↑(i+1) : ℂ)‖ = (↑(i+1):ℝ) := by rw [Complex.norm_natCast]
  rw [hz]; refine (mul_le_mul_of_nonneg_left ht (inv_nonneg.mpr (by positivity))).trans_eq ?_
  field_simp

/-- Marker-derivative costs retained with actual weights; applies when those budgets have
    been paid (or separately restrict to the needed marker set). Setting real/coupling-relative
    normalization and supplying accurate `ε,z` at the desired volume is analytic work, not a
    result of this theorem. No growth in the dimension of the marker ring except through the
    explicit bills and declared load `a`. -/
theorem log_mark_pay {x : Grade R r} (h : UnitLeading x) (hx : Symmetric x) (g : ℂ)
    {z : ℝ} (hg : ‖g‖≤z) (a : ℕ) (ha : ∀ t:R.Mode,t.val.card≤a)
    (F : Poly R) (hF : F.part R.quiet≠0) {ε M : ℝ} (w : V→ℝ) (hw : ∀ i,0<w i)
    (hf : Poly.price w (1-unitScale F)≤M) (he : Poly.price w (1-value g (ratio x))≤M)
    (hq : Poly.price w (unitScale F-value g (ratio x))≤ε) :
    Poly.price w (connected (unitScale F) - value g (logMarked x)) ≤ repeats a M*ε +
      ‖g‖^(r+1)*subtotal w r z (logSeries (a+r) (render (ratio x))) := by
  let Q:= omitted r g (logSeries (a+r) (render (ratio x)))
  have hM:= (Poly.nonnegative hw _).trans hf
  have H := log_mark_defect h hx g a ha
  calc
    _ = Poly.price w (connected (unitScale F)-connected (value g (ratio x)) + Q) := by rw [H]; congr 1; unfold Q; abel
    _ ≤ _ := (Poly.addition hw ..).trans (add_le_add ((lip _ _ w hw (unitScore hF) (leading_trunc_value (ratio_pure h) _) hf he a ha).trans
      (mul_le_mul_of_nonneg_left hq (repeats_pos a M hM))) (tail_bound w hw r z _ g hg))
end Lipschitz
end YM.Comparison.RG02.Order
