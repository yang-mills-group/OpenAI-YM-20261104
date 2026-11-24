import YM.Integration.OriginalCensusBarcode
import YM.Integration.OriginalWilsonMarginal

/-! The literal first Wilson block and its retained vacuum action on local
fields. The exact error is the known, signed, paid native high carrier. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalWilsonCensusStep

open Filter Lattice Wilson WilsonStartup RG RG.Shoot Marker
open AnalyticBridge VerifiedReset Collection
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open RG01Estimate RG01Estimate.CensusStep ConnectedActivityE6.Coat Push.SectorMeasure
open IterationFour IterationFour.Vacuum Extra.Iteration UVNext.CouplingReset
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open WilsonLimitConstruction.FundedCensusVacuum Pert.Asymptotics
open scoped Topology

variable {G : Gauge} {V : Type} {J : Request V}

/-- One actual conditional kernel applied to the literal Haar Wilson
weight, with its kernel and bare inverse couplings displayed independently. -/
def block (R : Run G) (m per : ℕ) (b β : ℝ) : Config G (R.family.side m per) → ℝ :=
  (R.family.path.levels.clock.op m per).push b (bare β)

def actual (R : Run G) (m per : ℕ) : Config G (R.family.side m per) → ℝ :=
  block R m per (R.family.path.β (m+1) per (m+1)) (R.family.beta (m+1) per)

theorem recorded (R : Run G) (m per : ℕ) :
    (R.family.path.rep (m+1) per m).eval = actual R m per := by
  let op := R.family.path.levels.clock.op m per
  let b := R.family.path.β (m+1) per (m+1)
  have htop : (R.family.path.rep (m+1) per (m+1)).eval = bare (R.family.beta (m+1) per) :=
    (R.makes.wilson.starts (m+1) per).2
  calc
    _ = op.push b (R.family.path.rep (m+1) per (m+1)).eval :=
      (R.makes.wilson.steps (m+1) per m (Nat.lt_succ_self m)).1
    _ = _ := congrArg (op.push b) htop

theorem positive (R : Run G) (m per : ℕ) (z : Config G (R.family.side m per)) :
    0 < actual R m per z := by
  rw [←recorded]
  exact Multi.AxisShift.chosen_positive R.makes.wilson (Nat.le_succ m) z

/-- The centered low action of this same first-step Census is evaluated
on a common physical field before taking any formal coefficients. -/
def keptAction (R : Run G) (m per r : ℕ) (z : Config G (R.family.side m per)) : ℝ :=
  let S := station R (m+1) per m (Nat.lt_succ_self m)
  let X := ledger R.kit S.guide
  let D := discarded R.kit S.guide S.guide S.identity r
  let Y := R.family.path.rep (m+1) per m
  let b := Y.beta - Averaging.delta (X.read D)
  WilsonLimitConstruction.FundedCensusComparison.action S r b z

variable {n : Side}

theorem normalize (Z : Rep G n) {σ C Λ δ w : ℝ} (hZ : Z.Lawful σ C Λ δ w)
    (D f : Config G n → ℝ) (h : ∀ z, D z = Z.eval z*Real.exp (-(f z-f 1)))
    (z : Config G n) (hz : flags Z.p.threshold z = ∅) :
    Real.log (D 1) - Real.log (D z) - Z.path.inChannels Z.clip Z.p Z.beta z -
      (f z-f 1) = Z.activities.additive Z.p z := by
  rw [h 1,h z,sub_self,neg_zero,Real.exp_zero,mul_one,
    SectorNext.Vacuum.flat_density Z hZ,Real.log_exp,Rep.eval,
    Z.activities.gas_one Z.p hz,mul_one,←Real.exp_add,Real.log_exp]
  unfold Rep.exponent Rep.scalar
  ring

def Receipt (R : Run G) (A : NumericSchedule R.family J) (ε : ℝ) (m per : ℕ) : Prop :=
  let L := R.family.path.levels
  let Y := R.family.path.rep (m+1) per m
  let Z := OriginalCensusBarcode.carrier R A m (m+1) per (Nat.lt_succ_self m)
  let H := (2*gStep (R.family.path.rep (m+1) per (m+1)).beta)^(J.order+1)
  let price := ActualNextInheritedPrice.extractionFactor R A m*H
  let f := keptAction R m per J.order
  let D := actual R m per
  price ≤ ε*regulatorRun R.family (m+1) per m^((J.order:ℝ)+1-J.eta) ∧
    (NativeRequestedInputNorm.regularPayload Z.activities).Invoice (A.outputNorm m) price ∧
    Z.activities.KBound (A.outputNorm m) (L.clock.forcedAllowance m) ∧
    (∀ z, D z = Z.eval z*Real.exp (-(f z-f 1))) ∧
    ∀ z, flags Y.p.threshold z = ∅ →
      Real.log (D 1 / D z) - Y.path.inChannels Y.clip Y.p Y.beta z -
        (f z-f 1) = Z.activities.additive (A.outputNorm m) z

theorem atStation (R : Run G) (A : NumericSchedule R.family J) {ε : ℝ} (m per : ℕ)
    (hs : OriginalCensusFusion.AtStation R A ε m (m+1) per (Nat.lt_succ_self m)) :
    Receipt R A ε m per := by
  unfold Receipt
  intro L Y Z H price f D
  obtain ⟨hprice,hcenter⟩ := CenteredCensusVacuum.atStation R A ε m (m+1) per (Nat.lt_succ_self m) hs
  obtain ⟨_,hb,hw,hc,hq,ht,hZ,hI,he⟩ := hcenter Y.beta
  obtain ⟨O⟩ := Tree.select (L.clock.op m per).ratio (L.clock.op m per).patch.odd_side
  have hD (z) : D z = Z.eval z*Real.exp (-(f z-f 1)) :=
    (congrFun (recorded R m per) z).symm.trans ((he O).2 z)
  refine ⟨hprice,hI,hZ.labels.boundK,hD,fun z hz => ?_⟩
  change Z.path = Y.path at hw
  change Z.clip = Y.clip at hc
  change Z.beta = Y.beta at hb
  change Z.p.threshold = Y.p.threshold at ht
  have hkin : Z.path.inChannels Z.clip Z.p Z.beta z = Y.path.inChannels Y.clip Y.p Y.beta z := by
    rw [hw,hc,hb]
    exact SignedCensusActivities.channels _ _ _ _ ht _ _
  have hpos (x) : 0 < D x := positive R m per x
  rw [Real.log_div (hpos 1).ne' (hpos z).ne',←hkin]
  exact normalize Z hZ D f hD z (ht.symm ▸ hz)

theorem first (R : Run G) (A : NumericSchedule R.family J) {ε : ℝ}
    (h : OriginalCensusFusion.AtOrder R A ε) :
    ∀ᶠ m : ℕ in atTop, ∀ per, Receipt R A ε m per := by
  filter_upwards [h] with m hm per
  exact atStation R A m per (hm (m+1) per (Nat.lt_succ_self m))

end YM.Integration.OriginalWilsonCensusStep
end
