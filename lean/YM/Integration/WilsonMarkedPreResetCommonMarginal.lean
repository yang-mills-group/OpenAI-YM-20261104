import YM.Integration.WilsonVacuumPreResetIndependentMarginal

/-! A full occupied polynomial and its actual earlier quiet action in the common affine Gaussian.
The normalized output retains the same field-dependent quiet divisor. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMarkedPreResetCommonMarginal
open Function Matrix Lattice RG Exterior Wilson Precision Tree FreeResolvent Bloch PowerSeries
open FormalBulk08 FormalBulk08.Series FormalBulk08.Flat FormalBulk08.Reef FormalBulk08.Jets FormalBulk08.Orb FormalBulk08.Wick
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonConditionalTaylorWheelHaar
open WilsonVacuumPreResetIndependentIntegrand
open scoped Classical BigOperators Matrix

open WilsonVacuumPreResetIndependentMarginal

section probes
variable {I V Y:Type}
private theorem renamed (E:I≃V)(x:I→ℝ)(y:Y→ℝ)(p:MvPolynomial V (MvPolynomial Y ℝ)):
    MvPolynomial.eval x (MvPolynomial.map (MvPolynomial.eval y) (MvPolynomial.rename E.symm p))=
      MvPolynomial.eval (x ∘ E.symm) (MvPolynomial.map (MvPolynomial.eval y) p):=by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add,hp,hq]
  | mul_X p i hp => simp [hp]

private theorem jointly {P Q:MvPolynomial I (MvPolynomial Y ℝ)}
    (h:∀x:I→ℝ,∀y:Y→ℝ,MvPolynomial.eval x (MvPolynomial.map (MvPolynomial.eval y) P)=
      MvPolynomial.eval x (MvPolynomial.map (MvPolynomial.eval y) Q)):P=Q:=by
  classical
  have measured (y:Y→ℝ):MvPolynomial.map (MvPolynomial.eval y) P=
      MvPolynomial.map (MvPolynomial.eval y) Q:=MvPolynomial.funext (fun x=>h x y)
  ext1 m
  apply MvPolynomial.funext
  intro y
  simpa only [MvPolynomial.coeff_map] using congrArg (MvPolynomial.coeff m) (measured y)
end probes

variable {G:Gauge}{c f:Side}(S:StepData c f)(F:Forest S.ratio)
variable (M:Matrix (Body 1 f) (Body 1 c) ℝ)
variable (H:Hull (Pine G S F) (wire G c))
variable (dm:∀y:Rays (wire G c),(fun v=>traceP y (H.drift v))=Flat.rawMean G S F M *ᵥ y)

include dm in
theorem payload (T:Pap (wire G f)):
    PowerSeries.map (emer (Active G F) (wire G c)).toRingEquiv.toRingHom
      (loom (camSlice G S F (extractV G S F M)) T)=
      Turner.tunnelP (Reef.pines F).symm (toInk H (Reef.seat F T)):=by
  apply PowerSeries.ext
  intro e
  apply jointly
  intro x y
  rw [coeff_map,Turner.tunnelP,coeff_map]
  change MvPolynomial.eval x (MvPolynomial.map (MvPolynomial.eval y)
    (emer _ _ (coeff e (loom (camSlice G S F (extractV G S F M)) T))))=
    MvPolynomial.eval x (MvPolynomial.map (MvPolynomial.eval y) (MvPolynomial.rename (Reef.pines F).symm
      (coeff e (toInk H (Reef.seat F T)))))
  rw [separate,renamed]
  have read:=congrArg (coeff e) (direction H (x ∘ (Reef.pines F).symm) y (Reef.seat F T))
  simp only [observe,glimpse_coeff,traceP,MvPolynomial.aeval_eq_eval,coeff_map] at read
  rw [read]
  have coordinate:point S F M (Sum.elim x y)=Sum.elim
      (fun v=> (x ∘ (Reef.pines F).symm) v+traceP y (H.drift v)) y:=by
    funext i
    cases i with
    | inl v =>
      change x ((Reef.pines F).symm v)+(Flat.rawMean G S F M *ᵥ y) v=
        x ((Reef.pines F).symm v)+traceP y (H.drift v)
      rw [←dm y]
    | inr v => rfl
  simp only [traceP,MvPolynomial.aeval_eq_eval] at coordinate
  rw [←coordinate]
  exact WilsonVacuumPreResetIndependentIntegrand.marked S F M T (Sum.elim x y) e

variable (O:ChartRatio G)(law:LocalRatio O)(P:PChart G f)(shape:shellK 2 P)
variable (br:S.patch.Branches S.kernel G)(a:S.Choices)
include dm law shape br in
theorem joint (D:Saddle ℝ (Active G F))
    (cov:D.q=H.saddle.q.submatrix (Reef.pines F) (Reef.pines F))
    (solved:Solved H (Reef.flush F a O (-flash P))) (T:Pap (wire G f)):
    beam (variation D (wire G c)).call (PowerSeries.map (emer (Active G F) (wire G c)).toRingEquiv.toRingHom
      (expan (shot S F M O P)*loom (camSlice G S F (extractV G S F M)) T))=
      Orb.vocal H (Reef.flush F a O (-flash P))*Orb.flag H (Reef.flush F a O (-flash P)) (Reef.seat F T):=by
  let E:=Reef.pines (G:=G) F
  have zero:coeff 0 (shot S F M O P)=0:=by
    rw [shot,loom,coeff_map,coeff_zero_eq_constantCoeff_apply,flash_blank (pack_zero S law),map_zero]
  have quiet:=WilsonVacuumPreResetIndependentMarginal.polynomial S F M H dm O law P shape br a solved
  have marked:=payload S F M H dm T
  have common:(variation D (wire G c)).call=(variation (Turner.door E H.saddle) (wire G c)).call:=by
    change Wick.moment (MvPolynomial.C.mapMatrix D.q)=Wick.moment (MvPolynomial.C.mapMatrix _)
    rw [cov]
    rfl
  rw [map_mul,map_expan _ zero,quiet,marked]
  simp only [Turner.tunnelP]
  rw [←map_expan _ (Orb.plur H _ solved),←map_mul,common]
  exact (Turner.minted E H.saddle _).trans (Orb.normalization H _ solved _).symm

end YM.Integration.WilsonMarkedPreResetCommonMarginal
