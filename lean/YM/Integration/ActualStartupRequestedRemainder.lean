import YM.Integration.ActualStartupMaskedAction
import YM.IntegrationR2.Rose.Cred
import YM.RG17.Refresh
import YM.Integration.ActualRepeatedNorm

/-! The complete original startup chip paid at the fixed requested norm.
This applies the native fixed-order estimate on the original Run; it does
not ask for a new Standing receipt or discard any original masked row. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualStartupRequestedRemainder

open Function Filter Finset Lattice Wilson RG
open WilsonStartup WilsonStartup.Start WilsonStartup.IterationFour
open YM.IterationFour.Vacuum Padded Ovens Ovens.Pipes
open PhysicalNext.Repeat.Legato
open scoped Classical BigOperators Topology

variable {G : Gauge}

private theorem chip_tail (r : ℕ) (u : G.El) :
    chip G r (G.mat u) = Quad.Rose.stub (r + 2) u := by
  unfold chip
  rw [Quad.surplus_actual, Quad.k_actual, ← Quad.Rose.reveal4]
  unfold Quad.Rose.stub Quad.Rose.pre
  simp only [Pi.sub_apply]
  ring

private def tailPayload (n : Side) (c : Clip) (β : ℝ) (r : ℕ) :
    Payload G n :=
  ⟨(Rose.payload (Quad.Rose.jetTail G (r + 2)) n c β).reg,
    (Rose.payload (Quad.Rose.jetTail G (r + 2)) n c β).E⟩

private theorem slate_eq (n : Side) (c : Clip) (β : ℝ) (r : ℕ) :
    slate G n (Start.weight c β) (chip G r) =
      tailPayload n c β r := by
  unfold slate tailPayload
  congr 1
  funext i U
  simp only [Rose.payload, Ovens.Pipes.pours, Rose.leader]
  split
  · cases name (Sheet n) i with
    | inl m =>
      change Start.weight c β * chip G r (G.mat (faceValue U m.positive)) =
        Start.weight c β * Quad.Rose.stub (r + 2) (faceValue U m.positive)
      rw [chip_tail]
    | inr m => rfl
  rfl

private theorem invoice {n : Side} (p : BudgetPoint) (c : Clip)
    (β : ℝ) (r : ℕ) (hr : 2 ≤ r) (q : ℝ)
    (hprice : (Rose.payload (Quad.Rose.jetTail G (r + 2)) n c β).EBound p q) :
    (slate G n (Start.weight c β) (chip G r)).Invoice p q := by
  have he := slate_eq (G := G) n c β r
  have hf := Rose.regularFamily (b := p) (n := n)
    (Quad.Rose.jetTail G (r + 2)) (by omega) c β
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [he]
    exact hf.smooth i
  · intro i
    rw [he]
    exact hf.at_flat i
  · intro i
    rw [he]
    exact hf.vanish i
  · intro s b
    refine ⟨sends (sheetAction s b), fun i => ?_⟩
    unfold slate
    dsimp only [comp_apply]
    simp_rw [name_sends, eInfo_transport, fixed_sends]
    refine ⟨trivial, trivial, fun U => ?_⟩
    split
    · cases name (Sheet n) i with
      | inl m =>
        change Start.weight c β *
            element G (chip G r) (Key.perm s b m).positive U =
          Start.weight c β * element G (chip G r) m.positive (pull s b U)
        have ht (m : Key n) (U : Config G n) :
            element G (chip G r) m.positive U =
              element G (chip G r) m.root (m.frame U) :=
          (chip_stamp G r hr).turns ..
        rw [ht, Key.oriented, ht m (pull s b U)]
        rfl
      | inr m => rfl
    rfl
  · rw [he]
    exact hprice


/-- The cost of the complete original chip at fixed requested orders. -/
def cost (R : Run G) (r : ℕ) (eta : ℝ) (N : ℕ) : ℝ :=
  Rose.amt (R.family.path.levels.clock.hatBeta N) (r + 3) (eta / 2)

/-- The native fixed-order startup estimate pays the original chip directly.
No all-growing-order Standing receipt is required. One tail works for every
period, at the literal original threshold and cover scale. -/
theorem eventual_invoice (R : Run G) (hG : G.Simple)
    (fieldOrder distanceOrder : ℕ) (support : ℝ)
    (hfield : 6 ≤ fieldOrder) (hdistance : 2 ≤ distanceOrder)
    (hsupport : 0 < support) (r : ℕ) (hr : 2 ≤ r)
    (eta : ℝ) (heta : 0 < eta) (heta_one : eta < 1) :
    ∀ᶠ N : ℕ in atTop, ∀ p : ℕ,
      let Q := ActualRepeatedNorm.atLevel R.family
        fieldOrder distanceOrder support hfield hdistance hsupport N
      0 ≤ cost R r eta N ∧
      (ActualStartupMaskedAction.remainder R N p r).Invoice Q (cost R r eta N) ∧
      cost R r eta N ≤ (2 : ℝ) ^ ((r : ℝ) + 1 - eta) *
        Pert.Asymptotics.regulatorRun R.family N p N ^ ((r : ℝ) + 1 - eta) := by
  let A := R.family.path.levels
  let S : Stage :=
    { A.params 0 with
      order := fieldOrder
      power := distanceOrder
      supportExponent := support
      order_ge := hfield
      power_ge := hdistance
      price_pos := hsupport }
  have hdiv : Tendsto A.clock.hatBeta atTop atTop :=
    tendsto_atTop_add_const_left _ _
      (A.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos hG))
  have hfit := (Real.tendsto_log_atTop.comp hdiv).eventually
    (Rose.fit0 (eta / 2) (half_pos heta) (Quad.Rose.jetTail G (r + 2)) S)
  filter_upwards [hfit] with N hN p
  let Q := ActualRepeatedNorm.atLevel R.family
    fieldOrder distanceOrder support hfield hdistance hsupport N
  let x := A.clock.hatBeta N
  have hx : 0 < x := zero_lt_one.trans (A.fits.delayed N)
  have hroot : (Real.sqrt x)⁻¹ = Real.exp (-(Real.log x / 2)) := by
    rw [Real.exp_neg, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx]
    congr 2
    ring
  have hthreshold : Q.threshold = Timing.temp (Real.log x) := by
    change (Real.sqrt x)⁻¹ * Real.exp ((Real.log (Real.log x))^2) = _
    unfold Timing.temp
    rw [hroot, Real.exp_add]
  have hprice := hN Q rfl rfl rfl hthreshold
  simp only [Function.comp_apply,
    Real.exp_log (show 0 < A.clock.hatBeta N from hx)] at hprice
  have hband := (R.makes.wilson.represents N p N le_rfl).band
  have hbeta : 0 ≤ R.family.path.β N p N :=
    (half_pos hx).le.trans hband.1
  have hnorm : ‖R.family.path.β N p N‖ ≤ 2 * x := by
    rw [Real.norm_of_nonneg hbeta]
    exact hband.2
  have hclip : (A.params N).clip.direct ≤ 1 :=
    Push.PriceCompiler.Canonical.direct_le_one
      (R.alloy.B.support.cap N N le_rfl).metric
  have hi : (ActualStartupMaskedAction.remainder R N p r).Invoice Q
      (cost R r eta N) := by
    apply invoice Q _ _ r hr
    exact Rose.ink (Quad.Rose.jetTail G (r + 2))
      hprice.1 hclip hnorm hprice.2
  refine ⟨Real.rpow_nonneg hx.le _, hi, ?_⟩
  let z : ℝ := x ^ (-(1 / 2) : ℝ)
  let a : ℝ := (r : ℝ) + 1 - eta
  have ha : 0 ≤ a := by
    dsimp only [a]
    linarith [Nat.cast_nonneg (α := ℝ) r]
  have hz2 : z^2 = x⁻¹ := by
    unfold z
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le,
      show (-(1 / 2) : ℝ) * ((2 : ℕ) : ℝ) = -1 by norm_num]
    exact Real.rpow_neg_one ..
  have hb := RG17.payBand R (p := p) (show N ≤ N from le_rfl)
  have hsmall : x⁻¹ ≤ 2 * Pert.Asymptotics.regulatorRun R.family N p N ^ 2 :=
    hb.2.2
  have hz : z ≤ 2 * Pert.Asymptotics.regulatorRun R.family N p N := by
    nlinarith [hb.1]
  calc
    cost R r eta N = z^a := by
      change x ^ (1 - ((r + 3 : ℕ) : ℝ) / 2 + eta / 2) =
        (x ^ (-(1 / 2) : ℝ)) ^ a
      rw [← Real.rpow_mul hx.le]
      congr 1
      dsimp only [a]
      push_cast
      ring
    _ ≤ (2 * Pert.Asymptotics.regulatorRun R.family N p N)^a :=
      Real.rpow_le_rpow (Real.rpow_nonneg hx.le _) hz ha
    _ = (2 : ℝ)^a * Pert.Asymptotics.regulatorRun R.family N p N^a :=
      Real.mul_rpow (by norm_num) hb.1.le

end YM.Integration.ActualStartupRequestedRemainder
end
