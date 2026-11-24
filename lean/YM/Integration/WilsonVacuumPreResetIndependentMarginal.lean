import YM.Integration.WilsonVacuumPreResetIndependentIntegrand
import YM.FormalBulk08.Turner.Route

/-! The original Wick contraction of the entire nonbare action in active forest coordinates.
Both polynomial rings are compared on their joint fine and coarse coordinates before integration. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetIndependentMarginal
open Function Matrix Lattice RG Exterior Wilson Precision Tree FreeResolvent Bloch PowerSeries
open FormalBulk08 FormalBulk08.Series FormalBulk08.Flat FormalBulk08.Reef FormalBulk08.Jets FormalBulk08.Orb FormalBulk08.Wick
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonConditionalTaylorWheelHaar
open WilsonVacuumPreResetIndependentIntegrand
open scoped Classical BigOperators Matrix
section readings
variable {V I:Type}[Fintype V][DecidableEq V](H:Hull V I)
def entry : V ⊕ I → MvPolynomial V (MvPolynomial I ℝ) :=
  Sum.elim (fun v => MvPolynomial.X v + MvPolynomial.C (H.drift v))
    (fun i => MvPolynomial.C (MvPolynomial.X i))

theorem entered (T : Pap (V ⊕ I)) :
    toInk H T = PowerSeries.map (MvPolynomial.aeval (entry H)).toRingHom T := by
  have h : fueled H = PowerSeries.C ∘ entry H := by
    funext i
    cases i <;> simp [fueled, entry, boost]
  rw [toInk, h, roam, const_insertAt, pure_map]

theorem centered (p : Pap (V ⊕ I)) (solved : Solved H p) :
    Orb.positive H p = toInk H (p-C (coeff 0 p)) := by
  change coeff 0 (toInk H p) = _ at solved
  calc
    _ = toInk H p - C (coeff 0 (toInk H p)) := by
      rw [solved]
      simp only [Orb.positive,boost,PowerSeries.map_C,map_add]
      abel
    _ = _ := by rw [entered,entered]; simp only [map_sub,PowerSeries.map_C,PowerSeries.coeff_map]

def observe (y : I→ℝ) (T : Ink V I) :=
  PowerSeries.map (MvPolynomial.map (MvPolynomial.eval y)) T

theorem direction (x : Rays V) (y : Rays I) (T : Pap (V ⊕ I)) :
    glimpse x (observe y (toInk H T)) =
      glimpse (Sum.elim (fun v => x v + traceP y (H.drift v)) y) T := by
  ext n
  rw [glimpse_coeff,observe,PowerSeries.coeff_map,entered,PowerSeries.coeff_map,glimpse_coeff]
  have h := Orb.toInk_value x y H (C (coeff n T))
  have dy : (MvPolynomial.aeval y).toRingHom = MvPolynomial.eval y := by
    ext i <;> simp
  simpa only [entered, PowerSeries.map_C,PowerSeries.coeff_zero_C, Orb.duplex_def,dy] using h


end readings

section probes
variable {I V Y:Type}
theorem separate (z:I→ℝ) (y:Y→ℝ) (p:MvPolynomial (I⊕Y) ℝ):
    MvPolynomial.eval z (MvPolynomial.map (MvPolynomial.eval y) (emer I Y p))=
      MvPolynomial.eval (Sum.elim z y) p:=by
  induction p using MvPolynomial.induction_on with
  | C a => simp [emer]
  | add p q hp hq => simp only [map_add,hp,hq]
  | mul_X p i hp =>
    simp only [map_mul,hp]
    congr 1
    cases i <;> simp [emer]


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
variable (O:ChartRatio G)(law:LocalRatio O)(P:PChart G f)(shape:shellK 2 P)
variable (br:S.patch.Branches S.kernel G)(a:S.Choices)
include dm law shape br in
theorem polynomial (solved:Solved H (Reef.flush F a O (-flash P))):
    PowerSeries.map (emer (Active G F) (wire G c)).toRingEquiv.toRingHom (shot S F M O P)=
      Turner.tunnelP (Reef.pines F).symm (Orb.positive H (Reef.flush F a O (-flash P))):=by
  apply PowerSeries.ext
  intro e
  apply jointly
  intro x y
  rw [coeff_map,Turner.tunnelP,coeff_map]
  change MvPolynomial.eval x (MvPolynomial.map (MvPolynomial.eval y) (emer _ _ (coeff e (shot S F M O P))))=
    MvPolynomial.eval x (MvPolynomial.map (MvPolynomial.eval y) (MvPolynomial.rename (Reef.pines F).symm
      (coeff e (Orb.positive H (Reef.flush F a O (-flash P))))))
  rw [separate,renamed,centered H _ solved]
  have read:=congrArg (coeff e) (direction H (x ∘ (Reef.pines F).symm) y (remainder (Reef.flush F a O (-flash P))))
  simp only [observe,glimpse_coeff,traceP,MvPolynomial.aeval_eq_eval,coeff_map] at read
  change MvPolynomial.eval (Sum.elim x y) (coeff e (shot S F M O P))=
    MvPolynomial.eval (x ∘ (Reef.pines F).symm) (MvPolynomial.map (MvPolynomial.eval y)
      (coeff e (toInk H (remainder (Reef.flush F a O (-flash P))))))
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
  exact signed S F O law P shape br a M (Sum.elim x y) e

include dm law shape br in
theorem integrated (D:Saddle ℝ (Active G F))
    (cov:D.q=H.saddle.q.submatrix (Reef.pines F) (Reef.pines F))
    (solved:Solved H (Reef.flush F a O (-flash P))):
    beam (variation D (wire G c)).call (PowerSeries.map (emer (Active G F) (wire G c)).toRingEquiv.toRingHom
      (expan (shot S F M O P)))=Orb.vocal H (Reef.flush F a O (-flash P)):=by
  let E:=Reef.pines (G:=G) F
  have zero:coeff 0 (shot S F M O P)=0:=by
    rw [shot,loom,coeff_map,coeff_zero_eq_constantCoeff_apply,flash_blank (pack_zero S law),map_zero]
  have landed:=polynomial S F M H dm O law P shape br a solved
  rw [map_expan _ zero,landed,Turner.tunnelP,←map_expan _ (Orb.plur H _ solved)]
  have common:(variation D (wire G c)).call=(variation (Turner.door E H.saddle) (wire G c)).call:=by
    change Wick.moment (MvPolynomial.C.mapMatrix D.q)=Wick.moment (MvPolynomial.C.mapMatrix _)
    rw [cov]
    rfl
  rw [common]
  exact Turner.minted E H.saddle (expan (Orb.positive H _))
end YM.Integration.WilsonVacuumPreResetIndependentMarginal
