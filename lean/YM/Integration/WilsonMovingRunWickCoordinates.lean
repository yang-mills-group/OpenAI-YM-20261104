import YM.Integration.WilsonMovingWickReindex
import YM.Integration.WilsonMovingFiniteConditional
import YM.Integration.WilsonMovingFiniteAction
import YM.Integration.WilsonMovingAffineField

/-! Equality of the *normalized* independent and moving finite Wick
functionals at an actual step, all torus sizes and nonzero backgrounds. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingRunWickCoordinates
open Function Lattice Exterior Wilson RG Precision Tree Matrix Bloch Push.Uniform
open Comparison.RG02 FreeResolvent WilsonCoeffUV PhysicalNext.Repeat.Legato
open FormalBulk08 Flat Reef Orb Next.Free Jets MSbar.Rolling MSbar.Cacao PowerSeries
open WilsonMovingPolynomialPull WilsonConditionalTaylorWick
open scoped Classical Matrix BigOperators
variable {G : Gauge} {c f : Side} {S : StepData c f}

theorem injection (F : Forest S.ratio) :
    (straight F G).submatrix (WilsonMovingJointAction.index F) (pines F).symm =
      WilsonMovingFiniteConditional.lift (wire G c) (Pine G S F) := by
  ext i k
  cases i with
  | inl i =>
    change (LinearMap.toMatrix' (lowerCol (ι:=Primary c G) (τ:=Key F G)).toLinearMap)
      (Sum.inr ((pines F).symm i)) ((pines F).symm k) = if i=k then 1 else 0
    rw [LinearMap.toMatrix'_apply]
    change (Pi.single ((pines F).symm k) 1 : Key F G → ℝ) ((pines F).symm i) = _
    by_cases h : i=k
    · subst i
      rw [Pi.single_eq_same,if_pos rfl]
    · have hk : (pines (G:=G) F).symm i ≠ (pines F).symm k :=
        fun e => h ((pines (G:=G) F).symm.injective e)
      rw [Pi.single_eq_of_ne hk,if_neg h]
  | inr i =>
    change (LinearMap.toMatrix' (lowerCol (ι:=Primary c G) (τ:=Key F G)).toLinearMap)
      (Sum.inl ((WilsonMovingGaussianCoordinates.link G c).symm i)) ((pines F).symm k) = 0
    rw [LinearMap.toMatrix'_apply]
    rfl

variable (R : Run G) (N i per : ℕ) (hi : i<N)
    (F : Forest (R.family.path.levels.clock.op i per).ratio)
    (tag : (R.family.path.levels.clock.op i per).Choices)

include tag in
theorem coarse (u : Positions (Primary (R.family.S.side i per) G)) :
    let S := R.family.path.levels.clock.op i per
    let A := Bloch.installed S.ratio ((destination R.family.path.levels N i).duo
      R.family.path.levels.clock.kernel.penalty).A0
    let y := FreeResolvent.flatten (tint G (Body 1 (R.family.S.side i per)) u)
    (poring F (((RunFormalChain.fromRun R).step N i per hi).b F) *ᵥ u) ∘
      WilsonMovingJointAction.index F = Sum.elim (Flat.rawMean G S F A *ᵥ y) y := by
  intro S A y
  let K := (RunFormalChain.fromRun R).step N i per hi
  have hm : center F (K.b F) u = fun j => (Flat.rawMean G S F A *ᵥ y) (Reef.pines F j) :=
    WilsonMovingGaussianCoordinates.onRun R N i per hi F tag u
  unfold poring
  rw [LinearMap.toMatrix'_mulVec]
  funext v
  cases v with
  | inl j =>
    change center F (K.b F) u ((Reef.pines F).symm j) = (Flat.rawMean G S F A *ᵥ y) j
    simpa only [Equiv.apply_symm_apply] using congrFun hm ((Reef.pines F).symm j)
  | inr j => rfl

theorem precision :
    ((((RunFormalChain.fromRun R).step N i per hi).covariance F tag).submatrix
      (Reef.pines F).symm (Reef.pines F).symm) =
      (Flat.testPrecision G (R.family.path.levels.clock.op i per) F
        (destination R.family.path.levels N i).wing)⁻¹ := by
  rw [WilsonCommonConditionalGaussian.covariance R N i per hi F tag, Matrix.inv_submatrix_equiv]
  ext j k
  simp [Matrix.submatrix]

theorem source (u : Positions (Primary (R.family.S.side i per) G))
    (p q : Pap (wire G (R.family.S.side (i+1) per))) :
    let S := R.family.path.levels.clock.op i per
    let K := (RunFormalChain.fromRun R).step N i per hi
    let P := destination R.family.path.levels N i
    let A := Bloch.installed S.ratio (P.duo R.family.path.levels.clock.kernel.penalty).A0
    let y := FreeResolvent.flatten (tint G (Body 1 (R.family.S.side i per)) u)
    quotient (WilsonMovingFiniteConditional.lift (wire G (R.family.S.side i per)) _)
      (Sum.elim (Flat.rawMean G S F A *ᵥ y) y) (Flat.testPrecision G S F P.wing)⁻¹
      (WilsonMovingFiniteConditional.interaction (Reef.flush F tag R.metals.O p)) (Reef.seat F q) =
    quotient (straight F G) (poring F (K.b F) *ᵥ u) (K.covariance F tag)
      (barbed F tag R.metals.O (splitV (place (WilsonMovingGaussianCoordinates.link G _).symm p)))
      (PowerSeries.map (rail (taps F G)).toRingHom (place (WilsonMovingGaussianCoordinates.link G _).symm q)) := by
  intro S K P A y
  let U := Reef.flush F tag R.metals.O p
  let s := WilsonMovingJointAction.index (G:=G) F
  have booked := WilsonMovingWickReindex.normalized (straight F G) (poring F (K.b F) *ᵥ u)
    (K.covariance F tag) (K.positive F tag) s (Reef.pines F).symm
    (WilsonMovingFiniteConditional.interaction U) (Reef.seat F q)
  have active : place s (WilsonMovingFiniteConditional.interaction U) = splitV (place s U) := by
    simp [place,WilsonMovingFiniteConditional.interaction,splitV,PowerSeries.coeff_map]
  rw [injection,coarse R N i per hi F tag u,precision R N i per hi F tag,active,
    WilsonMovingFiniteAction.positive F p K.branches tag R.metals.O R.alloy.B.ratio,
    WilsonMovingFiniteAction.inherited F q] at booked
  exact booked

end YM.Integration.WilsonMovingRunWickCoordinates
end
