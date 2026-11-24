import YM.Integration.WilsonConditionalTaylorWheelCommonInput
import YM.Integration.WilsonConditionalTaylorWheelDeposit

/-! The complete normalized physical upper response on its one original
Gaussian, before any change of the previous vacuum or of the marked input. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorWheelResponse
open Function Matrix Lattice RG Exterior Wilson Precision Tree FreeResolvent Bloch PowerSeries
open FormalBulk08 FormalBulk08.Flat FormalBulk08.Reef FormalBulk08.Jets FormalBulk08.Orb FormalBulk08.Series
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonConditionalTaylorWheelHaar WilsonConditionalTaylorWheelCommonInput
open MSbar.Cacao
open scoped Classical BigOperators Matrix
variable {G:Gauge} {c f:Side} (S:StepData c f) (F:Forest S.ratio)

def lift : Matrix (Pine G S F⊕wire G c) (Active G F) ℝ:=
  (WilsonMovingFiniteConditional.lift (wire G c) (Pine G S F)).submatrix id (Reef.pines F)

def center (M:Matrix (Body 1 f) (Body 1 c) ℝ) (y:wire G c→ℝ): Pine G S F⊕wire G c→ℝ:=
  Sum.elim (Flat.rawMean G S F M *ᵥ y) y

theorem received (M:Matrix (Body 1 f) (Body 1 c) ℝ) (y:wire G c→ℝ) (T:Pap (Active G F⊕wire G c))
    (U:Pap (Pine G S F⊕wire G c)) (agree:∀ e z, MvPolynomial.eval z (coeff e T)=
      MvPolynomial.eval (point (G:=G) S F M z) (coeff e U)):
    PowerSeries.map (WilsonMovingWickCoefficient.affine (WilsonMovingFiniteConditional.lift
      (wire G c) (Active G F)) (Sum.elim 0 y)).toRingHom T =
    PowerSeries.map (WilsonMovingWickCoefficient.affine (lift (G:=G) S F) (center (G:=G) S F M y)).toRingHom U:=by
  ext1 e
  simp only [coeff_map]
  apply MvPolynomial.funext
  intro z
  change MvPolynomial.eval z (WilsonMovingWickCoefficient.affine _ _ (coeff e T))=
    MvPolynomial.eval z (WilsonMovingWickCoefficient.affine _ _ (coeff e U))
  rw [WilsonMovingWickCoefficient.evaluated,WilsonMovingWickCoefficient.evaluated,agree]
  have h₀:Sum.elim (0:Active G F→ℝ) y+WilsonMovingFiniteConditional.lift (wire G c) (Active G F)*ᵥ z =
      Sum.elim z y:=by
    funext j;cases j <;> simp [WilsonMovingFiniteConditional.lift,Matrix.mulVec,dotProduct]
  rw [h₀]
  have hc:point (G:=G) S F M (Sum.elim z y)=center (G:=G) S F M y+lift (G:=G) S F*ᵥz:=by
    funext j
    cases j with
    | inl i =>
      change z ((Reef.pines F).symm i)+(Flat.rawMean G S F M*ᵥ y) i=
        (Flat.rawMean G S F M*ᵥ y) i + ∑ k,(if i=Reef.pines F k then (1:ℝ) else 0)*z k
      have source (k:Active G F):i=Reef.pines F k ↔ (Reef.pines F).symm i=k:=by
        constructor
        · rintro rfl; simp
        · intro h;rw [←h,Equiv.apply_symm_apply]
      rw [add_comm];congr 1
      simp [source]
    | inr i =>
      change y i=y i+∑k,(0:ℝ)*z k
      simp
  rw [hc]

theorem normalized (O:ChartRatio G) (law:LocalRatio O) (P:PChart G f) (degree:shellK 2 P)
    (branches:S.patch.Branches S.kernel G) (a:S.Choices) (M:Matrix (Body 1 f) (Body 1 c) ℝ)
    (y:wire G c→ℝ) (Q:Matrix (Active G F) (Active G F) ℝ) (T:Pap (wire G f)):
    WilsonConditionalTaylorWick.quotient (WilsonMovingFiniteConditional.lift (wire G c) (Active G F))
      (Sum.elim 0 y) Q (shot S F M O P) (loom (camSlice G S F (extractV G S F M)) T)=
    WilsonConditionalTaylorWick.quotient (lift (G:=G) S F) (center (G:=G) S F M y) Q
      (WilsonMovingFiniteConditional.interaction (Reef.flush F a O (-flash P))) (Reef.seat F T):=by
  have hf:=received S F M y _ _ (fun e z=>signed S F O law P degree branches a M z e)
  have ht:=received S F M y _ _ (fun e z=>marked S F M T z e)
  simp only [WilsonConditionalTaylorWick.quotient,WilsonConditionalTaylorWick.contract,map_mul,←sunshine,hf,ht]

end YM.Integration.WilsonConditionalTaylorWheelResponse
end

