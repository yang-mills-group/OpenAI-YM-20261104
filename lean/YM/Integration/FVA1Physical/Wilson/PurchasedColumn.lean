import YM.Integration.FVA1Physical.Wilson.PurchasedStencil
import YM.Integration.FVA1Physical.Wilson.TiltStencil
import YM.MSbar.Lapaz.Scrolls

/-! Unrestricted-period coefficientwise comparison for the genuine normalized
Wilson insertion of a fixed jointly supported action and source. Actual and
exterior-free slots use the measured coupling and the same conditional Hessian. -/
set_option autoImplicit false
set_option maxHeartbeats 550000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Matrix Function Filter MeasureTheory Set Finset Lattice RG YM.Wilson Tree Precision Exterior
open MSbar MSbar.Heath MSbar.Heath.Cottage MSbar.Heath.Stock MSbar.Whisk MSbar.Bulk MSbar.Mosaic MSbar.Bakery.Film MSbar.Kelvin
open MSbar.Lis MSbar.Cacao Push.Uniform Next.SectorChange RGComparison.Core16 Pressure
open scoped Classical Topology
variable {G : Gauge} {σ ι : Type} [Fintype σ] [DecidableEq σ]

def localColumn [Fintype ι] [DecidableEq ι] (s : σ→ι) (x : View σ)
    (C : Matrix ι ι ℝ) (f F : PowerSeries (Pot σ)) (p : ℕ) :=
  Lapaz.owes (imbed s).transpose C f F x p

lemma localColumn_coefficient [Fintype ι] [DecidableEq ι] (s : σ→ι) (x : View σ)
    {C : Matrix ι ι ℝ} (hc : C.PosDef) (f F : PowerSeries (Pot σ)) (hf : Kind f)
    {p n : ℕ} (hn : n≤p) :
    PowerSeries.coeff n (localColumn s x C f F p) =
      MvPolynomial.eval (parameters x (C.submatrix s s)) (PowerSeries.coeff n (tiltedStencil f F)) := by
  unfold localColumn Lapaz.owes Bakery.Portal.picture
  rw [PowerSeries.coeff_map]
  have h:=(tiltedStencil_eq_grow (imbed s).transpose x hc f F hf (p+1) n (by omega)).symm
  simpa only [Matrix.transpose_transpose,←clipped,pinch] using h

theorem purchased_wilson_column (J : Voice G) (clear : Clear G J) (χ : ChartRatio G) (hχ : LocalRatio χ)
    (simple : G.Simple) (H H' : Stage) (P : Patch) (K : KernelChoices) (branch : P.Branches K G)
    (f F : PowerSeries (Pot σ)) (hf : Kind f) (p n Q : ℕ) (hn : n≤p) {D : ℝ} (hD : 0≤D) :
    ∀ᶠ x:ℝ in atTop, ∀ (A : Mosaic.Issue G) (z : Positions (Primary A.c G)) (b : Site A.f),
      A.S.patch=P → A.S.kernel=K → Season J H H' x A.pre A.post A.S (courage G P.L x) →
      ‖z‖≤A.fClock*D →
      let y:=tip G P.L x
      let idx:=includeX (G:=G) A.F (boxX y b)
      let O:=represent (tint G (Exterior.Body 1 A.c) z)
      let ν:=vest (priced A.F A.v A.pre.clip A.pre.path) z
      let Hm:=mold A.pre A.F A.v
      ∀ (s : σ→Lake A.F (boxX y b) G),
      (∀ i, 2*separation b (address A.F G (Sum.inr (idx (s i)))) ≤ spotN y) →
      ∀ U∈hotel A.F (boxX y b) (boxY y b) J O ν (pillow y) (room y),
      let inside := fun i=>A.fClock⁻¹*interiorCoordinate A J y z b U (idx (s i))
      let far := fun i=>A.fClock⁻¹*bulkCoordinate A z (idx (s i))
      |PowerSeries.coeff n (localColumn s inside ((pinch idx Hm)⁻¹) f F p) -
        PowerSeries.coeff n (localColumn (idx ∘ s) far Hm⁻¹ f F p)| ≤ y^(-(Q:ℝ)) := by
  filter_upwards [purchased_parameters J clear χ hχ simple H H' P K branch
    (PowerSeries.coeff n (tiltedStencil f F)) Q hD] with x paid
  intro A z b patch kernel season hz y idx O ν Hm s near U hotel inside far
  obtain ⟨pos,bound⟩:=paid A z b patch kernel season hz s near U hotel
  have hp : ((pinch idx Hm)⁻¹).PosDef := (pos.submatrix (secureY A.F (boxX y b) G)).inv
  rw [localColumn_coefficient s _ hp f F hf hn,
    localColumn_coefficient _ _ pos.inv f F hf hn]
  exact bound

end YM.Integration.FVA1Physical.Wilson
