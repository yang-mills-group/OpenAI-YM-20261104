import YM.Integration.PhysicalAffineScalarClockCost

/-! Purchase of the physical scalar temperature threshold before each
admitted transition. Both source and cutoff price maps are unchanged. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
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

def cutoff (Pt : Teller G) (L : Side) := min (ConditionalAffineSourcePrices.rate Pt L) (Pt.top.width/4)

theorem cutoff_pos (Pt : Teller G) (L : Side) : 0<cutoff Pt L :=
  lt_min (ConditionalAffineSourcePrices.rate_pos Pt L) (div_pos Pt.top.width_pos (by norm_num))

def Paid (n : ℕ→ℕ→ℕ) : Prediction G := fun {M} {D} {A} _ =>
  ∀ j x, A.delay.betaEntry j ≤ x → ∀ i (st : StepStages j i) (fr : M.p.first ≤ i),
    let L := (Clockwork.patch D st fr).L
    Hot G L (n j i) (cutoff (query M.p M.K j i) L) x

theorem prepaid (n : ℕ→ℕ→ℕ) (s : Sheet G) (K : MapPrices) : Prepaid (Paid n) s K := by
  intro _ _ _ _ _ _ _
  refine ⟨fun _ => 0,fun l _ D _ _ _ _ _ protection _ _ V _ => ?_⟩
  let s' := ThroughLaunch.raise s l
  let test (j : ℕ) (x : ℝ) := ∀ i (st : StepStages j i) (fr : s'.first ≤ i),
    let L := (Clockwork.patch D st fr).L
    Hot G L (n j i) (cutoff (query s' K j i) L) x
  have H (j : ℕ) : ∀ᶠ x : ℝ in atTop, test j x := by
    let E (i : ℕ) (x : ℝ) := ∀ (st : StepStages j i) (fr : s'.first ≤ i),
      let L := (Clockwork.patch D st fr).L
      Hot G L (n j i) (cutoff (query s' K j i) L) x
    have prices (i : ℕ) (st : StepStages j i) : ∀ᶠ x : ℝ in atTop, E i x := by
      by_cases hfr : s'.first ≤ i
      · let L := (Clockwork.patch D st hfr).L
        exact (hot G L (n j i) (cutoff_pos (query s' K j i) L)).mono fun _ hx _ _ => hx
      · exact Eventually.of_forall fun _ _ fr => (hfr fr).elim
    exact (eventually_transitions j atTop E prices).mono fun _ hs i st fr => hs i st st fr
  obtain ⟨β,_,hβ,ready⟩ := collect_upper V.betaEntry test H
  let W : Delays protection := {V with betaEntry:=β}
  refine ⟨W,⟨hβ,le_rfl,le_rfl,le_rfl⟩,fun W' hW _ _ _ _ => ?_⟩
  intros
  exact fun j x hx => ready j x ((hW.beta j).trans hx)

theorem allPrices (n : ℕ→ℕ→ℕ) : FundedPredictionSupply.AllPrices (@Paid G n) := fun s _ => prepaid n s _

theorem both (n : ℕ→ℕ→ℕ) : FundedPredictionSupply.AllPrices
    (@FundedPredictionSupply.Both G (@ManuscriptQLocalScalarSourcePurchase.Paid G n) (@Paid G n)) :=
  fun s K => FundedPredictionSupply.both (ManuscriptQLocalScalarSourcePurchase.allPrices n s K) (allPrices n s K)

theorem realized (R : Run G) {n : ℕ→ℕ→ℕ} (paid : Paid n R.kit) (N m p : ℕ) (hm : m<N) :
    let S := R.family.path.levels.clock.op m p
    let x := R.alloy.B.a.clock.hatBeta m
    let j := R.alloy.B.a.clock.J (m+1)
    let i := R.alloy.B.a.clock.J m
    Hot G S.patch.L (n j i) (cutoff (query R.metals.p R.metals.K j i) S.patch.L) x := by
  intro S x j i
  let B := R.alloy.B
  have st := step_paid B.a m
  have fr := first_le B.valid m
  have hL : S.patch.L=R.rolls.L j := block_eq B.valid m
  have hJ : S.patch.J=j := (Testing.proceeds B N m p hm).atStep
  have hP : S.patch=Clockwork.patch R.rolls st fr := by
    cases h : S.patch; rw [h] at hL hJ; unfold Clockwork.patch; congr
  rw [hP]
  exact paid j x (B.valid.pays m) i st fr

/-- The thermal coefficient is from the independently stored fine input
used by Marked.honored on this same Run. -/
theorem band (R : Run G) (N m p : ℕ) (hm : m<N) :
    let S := R.family.path.levels.clock.op m p
    let β := (R.family.path.rep N p (m+1)).beta
    let x := R.alloy.B.a.clock.hatBeta m
    0<β ∧ β≤4*Pressure.betaF G x S.patch.L := by
  intro S β x
  let t := R.family.path.levels.clock.hatBeta (m+1)
  have ht : 0<t := WardBin.hot R.family.path.levels (m+1)
  have hf := (Weather.into_band R.family R.makes (m:=m+1) (N:=N) hm p).1
  change (Real.sqrt t)⁻¹/2≤(Real.sqrt β)⁻¹ at hf
  have hst := Real.sqrt_pos.mpr ht
  have hsb : 0<Real.sqrt β := inv_pos.mp ((half_pos (inv_pos.mpr hst)).trans_le hf)
  have hβ := Real.sqrt_pos.mp hsb
  have h₁ : Real.sqrt β≤2*Real.sqrt t := by
    have h' : (2*Real.sqrt t)⁻¹≤(Real.sqrt β)⁻¹ := by simpa only [mul_inv_rev,div_eq_mul_inv] using hf
    exact (inv_le_inv₀ (mul_pos (by norm_num) hst) hsb).mp h'
  have hL : S.patch.L=R.rolls.L (R.alloy.B.a.clock.J (m+1)) := block_eq R.alloy.B.valid m
  have hθ : t=Pressure.betaF G x S.patch.L := by rw [hL]; exact beta_eq R.alloy.B.valid m
  refine ⟨hβ,?_⟩
  calc β = (Real.sqrt β)^2 := (Real.sq_sqrt hβ.le).symm
       _ ≤ (2*Real.sqrt t)^2 := pow_le_pow_left₀ hsb.le h₁ 2
       _ = 4*(Pressure.betaF G x S.patch.L) := by rw [mul_pow,Real.sq_sqrt ht.le,←hθ]; ring

end YM.Integration.ManuscriptQLocalScalarClockPurchase

