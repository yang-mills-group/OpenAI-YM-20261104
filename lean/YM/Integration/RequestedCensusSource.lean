import YM.Integration.NativeRequestedInputNorm
import YM.Integration.CappedRegularReset
import YM.Integration.NativeCanonicalResetNorm

/-! The original signed source and the full forced family, inspected at a
weaker requested norm before scalar and kinetic extraction. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.RequestedCensusSource

open Lattice Wilson RG AnalyticBridge VerifiedReset Collection
open Push.AbsoluteSums Geo WilsonStartup Averaging Ovens Ovens.Pipes Progress.DirectedRecipe IterationFour.Vacuum
open scoped Classical

variable {G : Gauge} {n : Side}

private theorem regular_lower {n : Side} {p q : BudgetPoint}
    (hthreshold : q.threshold = p.threshold) (horder : q.order ≤ p.order)
    {S : Support n} {F : Config G n → ℝ} (h : p.Regular S F) :
    q.Regular S F := by
  refine ⟨h.sites, h.borel, h.symmetry, ?_, ?_⟩
  · intro U hU
    have hpU : Healthy p.threshold S U := hthreshold ▸ hU
    exact (h.smooth U hpU).of_le (by exact_mod_cast horder)
  · intro U hU D l hl
    exact h.hasDerivs U (hthreshold ▸ hU) D l (lt_of_lt_of_le hl horder)

private theorem bound_lower {n : Side} {p q : BudgetPoint}
    (hthreshold : q.threshold = p.threshold) (horder : q.order ≤ p.order)
    (hpower : q.power ≤ p.power) {o : Site n} {S : Support n}
    {F : Config G n → ℝ} {c : ℝ} (h : p.supBounds o S F c) :
    q.supBounds o S F c := by
  refine ⟨h.1, ?_⟩
  intro U hU l hl hD
  apply h.2 U (hthreshold ▸ hU) l (hl.trans horder)
  intro D hDl e
  have hd := hD D hDl e
  rw [hthreshold] at hd
  exact hd.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀
      (le_add_of_nonneg_right (Nat.cast_nonneg (separation e.1 o))) hpower)
    p.threshold_pos.le)

private theorem smaller_weight {ι : Type*} (keep : ι → Prop)
    [DecidablePred keep] (d : ι → ℕ) {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    {a b c : ℝ} (hab : a ≤ b)
    (h : SumBudget (fun i => if keep i then w i * Real.exp (b*d i) else 0) c) :
    SumBudget (fun i => if keep i then w i * Real.exp (a*d i) else 0) c := by
  apply budget_mono h
  · intro i
    split
    · exact mul_nonneg (hw i) (Real.exp_pos _).le
    · rfl
  · intro i
    split
    · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right hab (Nat.cast_nonneg _))) (hw i)
    · rfl

/-- The same addresses and signed functions at the requested norm. Both
the early three-unit reserve and the one-unit forced reserve are retained. -/
theorem restrict {X : Listing G n} {v : Source G n} {p q : BudgetPoint}
    {H w : ℝ} (h : Local X p v H w)
    (hthreshold : q.threshold = p.threshold) (hblock : q.B = p.B)
    (horder : q.order ≤ p.order) (hpower : q.power ≤ p.power)
    (hsupport : q.supportExponent ≤ p.supportExponent) : Local X q v H w := by
  refine ⟨fun i => regular_lower hthreshold horder (h.smooth i), ?_, h.transforms, ?_, ?_⟩
  · refine ⟨h.family.sym, h.family.symtest, h.family.meas, h.family.meas_test, ?_, ?_, ?_⟩
    · simpa only [hthreshold] using h.family.reads
    · simpa only [hthreshold] using h.family.reads_test
    · simpa only [hthreshold] using h.family.permit
  · obtain ⟨u, hu, he⟩ := h.cheap
    refine ⟨u, fun i => bound_lower hthreshold horder hpower (hu i), ?_⟩
    intro x
    unfold Quotes.preExponent
    rw [hblock]
    exact smaller_weight (fun i => (X.reg i).site = x)
      (fun i => coverNumber p.B (X.reg i).support) (fun i => (hu i).1)
      (add_le_add hsupport (le_refl (3 : ℝ))) (he x)
  · obtain ⟨k, hk, hK⟩ := h.expensive
    refine ⟨k, hk, ?_⟩
    intro x
    rw [hblock]
    exact smaller_weight (fun i => x ∈ (X.hard i).support)
      (fun i => coverNumber p.B (X.hard i).support) (fun i => (hk i).1)
      (add_le_add hsupport (le_refl (1 : ℝ))) (hK x)

/-- The physical signed fieldwise additive action depends on the threshold
only. Every original mask, including on a flagged field, is unchanged. -/
theorem action {X : Listing G n} {v : Source G n} {p q : BudgetPoint}
    (ht : q.threshold = p.threshold) (U : Config G n) :
    (X.read v).additive q U = (X.read v).additive p U :=
  NativeRequestedInputNorm.amount_eq (NativeRequestedInputNorm.regularPayload (X.read v)) ht U

/-- At a fixed finite requested order, the actual scalar/kinetic shell has
an affine-null regular invoice and its full forced bound. -/
theorem reset {X : Listing G n} {v : Source G n} {p q : BudgetPoint}
    {W : PathData G} {clip : Clip} {σ C Λ H w : ℝ}
    (hG : G.Simple) (hn : 20 < n.val) (hW : W.Bounds clip σ C Λ)
    (h : Local X p v H w) (ht : q.threshold = p.threshold) (hb : q.B = p.B)
    (ho : q.order ≤ p.order) (hp : q.power ≤ p.power)
    (hs : q.supportExponent ≤ p.supportExponent) (hc : Decent clip q)
    (hw : Width q clip σ) (β τ α : ℝ) :
    let T := VacuumGermReset.shell W clip q X v β τ α
    let charge := CappedRegularReset.regularNeed G q clip σ C 0 H
    T.Lawful σ C Λ charge w ∧
      (NativeRequestedInputNorm.regularPayload T.activities).Invoice q charge := by
  have hq := restrict h ht hb ho hp hs
  have hl := CappedRegularReset.lawful hG hn hW hq hc hw β τ α
  exact ⟨hl, NativeRequestedInputNorm.regular_invoice hl.labels rfl rfl le_rfl le_rfl le_rfl⟩

/-- The actual post-fusion drawer has the same affine-null regular price.
Only compensating zero regular rows are appended by its address map. -/
theorem after {n : Side} (W : PathData G) (c : Clip)
    (p : BudgetPoint) (X : Listing G n) (v : Collection.Source G n)
    (beta tau : Real) {d w : Real}
    (h : (VacuumGermReset.shell W c p X v beta tau 0).activities.Valid p d w) :
    (NativeRequestedInputNorm.regularPayload
      (Reset.after W c p X v beta tau 0).activities).Invoice p d ∧
      (Reset.after W c p X v beta tau 0).activities.EBound p d := by
  let Y := shelves X W p
  let T := Reset.reserve W c p X v 0 (delta (X.read v))
  have h0 : (Y.pours T).Valid p d w := h
  have hr := (Rack.preserves Y T p).regular h0.regular
  have hb := (Rack.preserves Y T p).Ebound h0.boundE
  refine ⟨?_, hb⟩
  refine {
    smooth := hr.smooth
    flat := hr.at_flat
    null := hr.vanish
    moves := ?_
    credit := hb }
  intro s b
  obtain ⟨e⟩ := h0.moves s b
  let e' := on_shelves e
  exact ⟨e'.ep, fun i => ⟨e'.reg_site i, e'.reg_support i, e'.valuesE i⟩⟩

end YM.Integration.RequestedCensusSource
end
