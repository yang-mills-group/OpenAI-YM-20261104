import YM.Integration.ManuscriptQLocalScalarClockPurchase
/-! The original uniform stage payment for an arbitrary fine-coupling power. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.PhysicalAffineScalarClockCost
open Filter Function Lattice RG Pressure Pressure.Stores FreeResolvent FreeResolvent.Affine
open Next.SectorChange AnalyticBridge.SectorAffine PhysicalAffineScalarResidualPrice
open PhysicalAffineScalarOperatorPrices PhysicalAffineScalarRootContraction ConnectedActivityE6
open scoped Topology Classical ContDiff BigOperators

variable {G : Gauge} {L : Side}

namespace Power
/-- A preassigned scalar tariff and coupling grade are absorbed on the
actual fine representative band, uniformly in the period and forest. -/
theorem fine_order (G : Gauge) (L : Side) (m : ℕ) (A κ : ℝ) (hκ : 0<κ) :
    ∀ᶠ x : ℝ in atTop, ∀ β : ℝ, 0<β → β≤4*betaF G x L →
      |A| * Real.exp (-κ*(till x:ℝ))≤(coupling β)^m := by
  have H := (constant (G:=G) (L:=L) 1).sum ((fine (G:=G) (L:=L)).scale 4)
  obtain ⟨a,h⟩ := H
  have P : Power G L (fun x => |A| * (1+4*betaF G x L)^m) :=
    (constant (G:=G) (L:=L) |A|).product ⟨_,h.pow m⟩
  filter_upwards [absorb P hκ] with x hx
  intro β hb hβ
  have hs : Real.sqrt β≤1+4*betaF G x L := by
    nlinarith [Real.sq_sqrt hb.le,sq_nonneg (Real.sqrt β-1/2)]
  have ht : Real.exp (-(κ/2)*(till x:ℝ))≤1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (half_pos hκ).le) (Nat.cast_nonneg _))
  have he : (|A| * Real.exp (-κ*(till x:ℝ)))*(Real.sqrt β)^m≤1 := by
    calc _ ≤ (|A| * Real.exp (-κ*(till x:ℝ)))*(1+4*betaF G x L)^m :=
           mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.sqrt_nonneg _) hs m)
             (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)
         _ = (|A| * (1+4*betaF G x L)^m)*Real.exp (-κ*(till x:ℝ)) := by ring
         _ ≤ _ := hx.trans ht
  unfold coupling
  rw [inv_pow,←one_div]
  exact (le_div_iff₀ (pow_pos (Real.sqrt_pos.mpr hb) m)).mpr he

end Power
end YM.Integration.PhysicalAffineScalarClockCost

namespace YM.Integration.ManuscriptQLocalScalarClockPurchase
open Filter Function Set Lattice Wilson RG Pressure Pressure.Testing Pressure.Tube Pressure.Stores
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open Org Input Push Push.PriceCompiler Push.SectorMeasure Next.SectorChange Next.SectorChange.Rows
open AnalyticBridge AnalyticBridge.GaussianFieldAlignment AnalyticBridge.SectorAffine
open Progress.DirectedRecipe RG.Shoot Next.SectorChange.Gaussian FreeResolvent FreeResolvent.Affine
open Pert.Asymptotics MatchingLedger.Compass.Income
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection PhysicalAffineScalarClockCost
open Precision RG.Supply
open scoped Classical Topology ContDiff Matrix.Norms.Frobenius
variable {G : Gauge}

private def stagePayment (test : Teller G → Patch → ℕ → ℕ → ℝ → Prop) : Prediction G :=
  fun {M} {D} {A} _ => ∀ j x, A.delay.betaEntry j≤x → ∀ i (st : StepStages j i) (fr : M.p.first ≤ i),
    test (query M.p M.K j i) (Clockwork.patch D st fr) j i x

private theorem purchase_stage (test : Teller G → Patch → ℕ → ℕ → ℝ → Prop)
    (late : ∀ Pt P j i, ∀ᶠ x : ℝ in atTop, test Pt P j i x) (s : Sheet G) (K : MapPrices) :
    Prepaid (stagePayment test) s K := by
  intro _ _ _ _ _ _ _
  refine ⟨fun _ => 0,fun l _ D _ _ _ _ _ protection _ _ V _ => ?_⟩
  let s' := ThroughLaunch.raise s l
  let criterion (j : ℕ) (x : ℝ) := ∀ i (st : StepStages j i) (fr : s'.first ≤ i),
    test (query s' K j i) (Clockwork.patch D st fr) j i x
  have H (j : ℕ) : ∀ᶠ x : ℝ in atTop, criterion j x := by
    let E (i : ℕ) (x : ℝ) := ∀ (st : StepStages j i) (fr : s'.first ≤ i),
      test (query s' K j i) (Clockwork.patch D st fr) j i x
    have prices (i : ℕ) (st : StepStages j i) : ∀ᶠ x : ℝ in atTop, E i x := by
      by_cases hfr : s'.first ≤ i
      · exact (late (query s' K j i) (Clockwork.patch D st hfr) j i).mono fun _ hx _ _ => hx
      · exact Eventually.of_forall fun _ _ fr => (hfr fr).elim
    exact (eventually_transitions j atTop E prices).mono fun _ hs i st fr => hs i st st fr
  obtain ⟨β,_,hβ,ready⟩ := collect_upper V.betaEntry criterion H
  let W : Delays protection := {V with betaEntry:=β}
  refine ⟨W,⟨hβ,le_rfl,le_rfl,le_rfl⟩,fun W' hW _ _ _ _ => ?_⟩
  intro alloy η reset exchange menu aux rider booth hp hy hm
  exact fun j x hx => ready j x ((hW.beta j).trans hx)

/-- A preassigned post-block scalar tariff is absorbed into any requested
coupling grade, for every late actual representative in its allowed band. -/
def Demand (amount : Teller G → Patch → ℕ → ℕ → ℝ) (order : ℕ→ℕ→ℕ) : Prediction G :=
  stagePayment fun Pt P j i x => ∀ β : ℝ, 0<β → β≤4*betaF G x P.L →
    |amount Pt P j i| * Real.exp (-(cutoff Pt P.L/4)*(till x:ℝ))≤(coupling β)^(order j i)

theorem demand_prepaid (amount : Teller G → Patch → ℕ → ℕ → ℝ) (order : ℕ→ℕ→ℕ)
    (s : Sheet G) (K : MapPrices) : Prepaid (Demand amount order) s K :=
  purchase_stage _ (fun Pt P j i => Power.fine_order G P.L (order j i) (amount Pt P j i) _
    (div_pos (cutoff_pos Pt P.L) (by norm_num))) s K

theorem demand_prices (amount : Teller G → Patch → ℕ → ℕ → ℝ) (order : ℕ→ℕ→ℕ) :
    FundedPredictionSupply.AllPrices (@Demand G amount order) := fun s _ => demand_prepaid amount order s _

theorem demand_realized (R : Run G) {amount : Teller G → Patch → ℕ → ℕ → ℝ} {order : ℕ→ℕ→ℕ}
    (paid : Demand amount order R.kit) (N m p : ℕ) (hm : m<N) :
    let P := Clockwork.patch R.rolls (step_paid R.alloy.B.a m) (first_le R.alloy.B.valid m)
    let x := R.alloy.B.a.clock.hatBeta m
    let j := R.alloy.B.a.clock.J (m+1)
    let i := R.alloy.B.a.clock.J m
    let Pt := query R.metals.p R.metals.K j i
    let β := (R.family.path.rep N p (m+1)).beta
    |amount Pt P j i| * Real.exp (-(cutoff Pt P.L/4)*(till x:ℝ))≤(coupling β)^(order j i) := by
  intro P x j i Pt β
  let S := R.family.path.levels.clock.op m p
  let B := R.alloy.B
  have st := step_paid B.a m
  have fr := first_le B.valid m
  have hL : S.patch.L=R.rolls.L j := block_eq B.valid m
  have hJ : S.patch.J=j := (Testing.proceeds B N m p hm).atStep
  have hP : S.patch=Clockwork.patch R.rolls st fr := by
    cases h : S.patch; rw [h] at hL hJ; unfold Clockwork.patch; congr
  have hband : 0<β ∧ β≤4*betaF G x S.patch.L := band R N m p hm
  exact paid j x (B.valid.pays m) i st fr β hband.1 (by simpa only [hP] using hband.2)

end YM.Integration.ManuscriptQLocalScalarClockPurchase
end

