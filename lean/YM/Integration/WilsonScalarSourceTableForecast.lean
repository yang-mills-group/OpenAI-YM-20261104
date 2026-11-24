import YM.Integration.ManuscriptQLocalStoredGaussianScalar
import YM.Integration.ManuscriptQLocalScalarClockDemand

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonScalarSourceTableForecast
open Function Filter Lattice Wilson RG Tree Precision Pressure Supply Testing Stores
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open Org Input Push Push.PriceCompiler Push.SectorMeasure Next.SectorChange Next.SectorChange.Rows
open AnalyticBridge AnalyticBridge.GaussianFieldAlignment AnalyticBridge.SectorAffine
open Progress.DirectedRecipe RG.Shoot Next.SectorChange.Gaussian FreeResolvent FreeResolvent.Affine
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open scoped Classical Topology ContDiff Matrix.Norms.Frobenius
open ManuscriptQLocalScalarSourcePurchase (Prices Offer Bought)
open ManuscriptQLocalScalarClockPurchase (cutoff cutoff_pos Demand)
open PhysicalAffineScalarClockCost
variable {G : Gauge}


/-- The same retained source pays the ordinary root, the spatially weighted changed root, and the radius conversion. -/
def fee (G : Gauge) (P : Patch) (Pt : Teller G) (n : ℕ) (r : Prices) : ℝ :=
  let s := ManuscriptQLocalStoredGaussianScalar.cutWidth G P Pt n r
  let ρ := ManuscriptQLocalStoredGaussianScalar.cutAllowance G P Pt n r
  let W := (max 1 (torusPay (PAC G 1) s)) ^ n
  max 1 (torusPay PUnit.{1} s) * W * |ρ| * Real.exp 1

private def bid (Pt : Teller G) (P : Patch) (n power : ℕ) (x : ℝ) (r : Prices) : Prop :=
  Offer Pt P n x r ∧ ∀ β : ℝ, 0 < β → β ≤ 4 * betaF G x P.L →
    |fee G P Pt n r| * Real.exp (-(cutoff Pt P.L/4)*(till x:ℝ)) ≤ (coupling β)^power

def Named (n : ℕ → ℕ → ℕ) (r : ℕ → ℕ → Prices) : Prediction G := fun {M} {D} {A} _ =>
  ∀ j x, A.delay.betaEntry j ≤ x → ∀ i (st : StepStages j i) (fr : M.p.first ≤ i),
    Offer (query M.p M.K j i) (Clockwork.patch D st fr) (n j i) x (r j i)

/-- A single stage table buys both comparisons for the same purchased numeric data. -/
def Paid (n power : ℕ → ℕ → ℕ) : Prediction G := fun {_} {_} {_} kit =>
  ∃ r : ℕ → ℕ → Prices, Named n r kit ∧
    Demand (fun Pt P j i => fee G P Pt (n j i) (r j i)) power kit

theorem prepaid (n power : ℕ → ℕ → ℕ) (s : Sheet G) (K : MapPrices) : Prepaid (Paid n power) s K := by
  intro _ _ _ _ _ _ _
  refine ⟨fun _ => 0,fun l _ D _ _ _ _ _ protection _ _ V _ => ?_⟩
  let s' := ThroughLaunch.raise s l
  have rows (j i : ℕ) : ∃ r : Prices, ∀ᶠ x : ℝ in atTop, ∀ (st : StepStages j i) (fr : s'.first ≤ i),
      bid (query s' K j i) (Clockwork.patch D st fr) (n j i) (power j i) x r := by
    by_cases hi : StepStages j i ∧ s'.first ≤ i
    · let P := Clockwork.patch D hi.1 hi.2
      obtain ⟨d,N,M,hd,hN,hM,H⟩ := PhysicalAffineScalarRetainedSource.full G P (query s' K j i) (s'.has P) (n j i)
      let r : Prices := ⟨d,N,M,hd,hN,hM⟩
      refine ⟨r,?_⟩
      have hf := Power.fine_order G P.L (power j i) (fee G P (query s' K j i) (n j i) r)
        (cutoff (query s' K j i) P.L/4) (div_pos (cutoff_pos _ _) (by norm_num))
      filter_upwards [H,monitors G P.L,hf] with x hx htmp hfee
      intro st fr
      refine ⟨⟨htmp.1,?_⟩,hfee⟩
      intro c f S T hS hT hc F k z
      simpa only [hS] using hx S T hS hT hc htmp.1 F k z
    · exact ⟨⟨1,1,1,zero_lt_one,zero_lt_one,zero_lt_one⟩,Eventually.of_forall fun _ st fr => False.elim (hi ⟨st,fr⟩)⟩
  choose r hr using rows
  have simultaneous (j : ℕ) : ∀ᶠ x : ℝ in atTop,
      ∀ i (st : StepStages j i) (fr : s'.first ≤ i),
        bid (query s' K j i) (Clockwork.patch D st fr) (n j i) (power j i) x (r j i) := by
    let E := fun (i : ℕ) (x : ℝ) => ∀ (st : StepStages j i) (fr : s'.first ≤ i),
      bid (query s' K j i) (Clockwork.patch D st fr) (n j i) (power j i) x (r j i)
    have prices := eventually_transitions j atTop E (fun i _ => hr j i)
    exact prices.mono fun x hx i st fr => hx i st st fr
  obtain ⟨β,_,hβ,ready⟩ := collect_upper V.betaEntry _ simultaneous
  let W : Delays protection := {V with betaEntry:=β}
  refine ⟨W,⟨hβ,le_rfl,le_rfl,le_rfl⟩,fun W' hW _ _ _ _ => ?_⟩
  intros
  refine ⟨r,?_,?_⟩
  · exact fun j x hx i st fr => (ready j x ((hW.beta j).trans hx) i st fr).1
  · exact fun j x hx i st fr => (ready j x ((hW.beta j).trans hx) i st fr).2

theorem prices (n power : ℕ → ℕ → ℕ) : FundedPredictionSupply.AllPrices (@Paid G n power) :=
  fun s _ => prepaid n power s _

theorem source (R : Run G) {n power : ℕ → ℕ → ℕ} (p : Paid n power R.kit) :
    ManuscriptQLocalScalarSourcePurchase.Paid n R.kit := ⟨p.choose,p.choose_spec.1⟩

theorem clock (R : Run G) {n power : ℕ → ℕ → ℕ} (p : Paid n power R.kit) :
    Demand (fun Pt P j i => fee G P Pt (n j i) (p.choose j i)) power R.kit := p.choose_spec.2

theorem realized (R : Run G) {n power : ℕ → ℕ → ℕ} (paid : Paid n power R.kit) (N m p : ℕ) (hm : m<N) :
    let S := R.alloy.B.a.clock.op m p
    let x := R.alloy.B.a.clock.hatBeta m
    let j := R.alloy.B.a.clock.J (m+1)
    let i := R.alloy.B.a.clock.J m
    let T := ships R.alloy.B N m p
    0<temp x ∧ Bought S T (query R.metals.p R.metals.K j i) (n j i) x (paid.choose j i) := by
  intro S x j i T
  let B := R.alloy.B
  have st := step_paid B.a m
  have fr := first_le B.valid m
  have hL : S.patch.L=R.rolls.L j := block_eq B.valid m
  have hJ : S.patch.J=j := (Testing.proceeds B N m p hm).atStep
  have hP : S.patch=Clockwork.patch R.rolls st fr := by
    cases h : S.patch
    rw [h] at hL hJ
    unfold Clockwork.patch
    congr
  have hs : 100*(1+radiusB x) ≤ (B.a.S.side m p).val := by rw [add_comm 1]; exact B.a.fits.sizeT m p
  have h := paid.choose_spec.1 j x (B.valid.pays m) i st fr
  exact ⟨h.1,h.2 S T hP (Testing.proceeds B N m p hm) hs⟩

end YM.Integration.WilsonScalarSourceTableForecast

