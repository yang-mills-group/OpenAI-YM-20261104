import YM.Integration.WilsonConditionalTaylorWheelReef
import YM.Integration.WilsonVacuumPreResetIndependentCoil

/-! Both original constructions use the identical full finite Gaussian
integrand on every physical scalar field and every retained source term. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetIndependentIntegrand
open Function Matrix Lattice RG Exterior Wilson Precision Tree FreeResolvent Bloch PowerSeries
open FormalBulk08 FormalBulk08.Flat FormalBulk08.Reef FormalBulk08.Jets FormalBulk08.Orb
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonConditionalTaylorWheelHaar
open Comparison.RG02 WilsonCoeffUV.Mer WilsonCoeffUV.Cosmos WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic Next.Free
open scoped Classical BigOperators Matrix
variable {G:Gauge} {c f:Side} (S:StepData c f) (F:Forest S.ratio)

def remainder {I:Type} (p:Pap I):Pap I:=p-PowerSeries.C (coeff 0 p)

def point (M:Matrix (Body 1 f) (Body 1 c) ℝ) (z:Active G F⊕Woods G c→ℝ):
    Pine G S F⊕wire G c→ℝ:=Sum.elim (drift (G:=G) S F M z) (rightArm z)

theorem signed (O:ChartRatio G) (law:LocalRatio O) (P:PChart G f) (degree:shellK 2 P)
    (branches:S.patch.Branches S.kernel G) (a:S.Choices) (M:Matrix (Body 1 f) (Body 1 c) ℝ)
    (z: Active G F⊕Woods G c→ℝ) (e:ℕ):
    MvPolynomial.eval z (coeff e (shot S F M O P))=
      MvPolynomial.eval (point (G:=G) S F M z) (coeff e
        (remainder (Reef.flush F a O (-flash P)))):=by
  by_cases zero:e=0
  · subst e
    have h:coeff 0 (shot S F M O P)=0:=by
      rw [shot,loom,coeff_map,coeff_zero_eq_constantCoeff_apply,flash_blank (pack_zero S law),map_zero]
    rw [h,remainder,map_sub,coeff_zero_C,sub_self,map_zero,map_zero]
  · have pos:0<e:=Nat.pos_of_ne_zero zero
    rw [WilsonConditionalTaylorWheelShot.original S F O law P degree branches a M z e pos,
      WilsonConditionalTaylorWheelReef.haar S F O law M z e,remainder,
      map_sub,coeff_C,if_neg zero,sub_zero,point,WilsonConditionalTaylorWheelReef.primitive S F O law,
      map_neg,map_neg]
    ring

theorem marked (M:Matrix (Body 1 f) (Body 1 c) ℝ) (T:Pap (wire G f))
    (z:Active G F⊕Woods G c→ℝ) (e:ℕ):
    MvPolynomial.eval z (coeff e (loom (camSlice G S F (extractV G S F M)) T))=
      MvPolynomial.eval (point (G:=G) S F M z) (coeff e (Reef.seat F T)):=by
  have h:=congrArg (coeff e) (WilsonMovingForestRestriction.seat F (point (G:=G) S F M z) T)
  rw [glimpse_coeff,glimpse_coeff] at h
  rw [loom,PowerSeries.coeff_map]
  change MvPolynomial.eval z (cord _ _)=_
  rw [cord_apply,WilsonConditionalTaylorWheelAffine.fine S F M z]
  exact h.symm

open WilsonConditionalTaylorWheelKernel in
theorem complete (R:PhysicalNext.Repeat.Legato.Run G)(simple:G.Simple)(N j per:ℕ)(live:j<N)
    (F:Forest (R.family.path.levels.clock.op j per).ratio)
    (a:(R.family.path.levels.clock.op j per).Choices)
    (z:Active G F⊕Woods G (R.family.side j per)→ℝ):
    let S:=R.family.path.levels.clock.op j per
    let M:=installed S.ratio (predictionA R.family.path.levels N j)
    let P:=WilsonCoeffUV.Winding.emera (actionW R.family.path.levels R.metals.O N (j+1)) (R.family.side (j+1) per)
    PowerSeries.map (MvPolynomial.eval z) (FormalBulk08.Series.expan (shot S F M R.metals.O P))=
      PowerSeries.map (MvPolynomial.eval (point S F M z)) (FormalBulk08.Series.expan (remainder (Reef.flush F a R.metals.O (-flash P)))):=by
  intro S M P
  have facts:=WilsonCoeffUV.Winding.emera_far R.family.path.levels simple R.alloy.B.ratio (Nat.succ_le_iff.mpr live) (R.family.side (j+1) per)
  have zero:coeff 0 (shot S F M R.metals.O P)=0:=by
    rw [shot,loom,coeff_map,coeff_zero_eq_constantCoeff_apply,flash_blank (pack_zero S R.alloy.B.ratio),map_zero]
  have other:coeff 0 (remainder (Reef.flush F a R.metals.O (-flash P)))=0:=by
    rw [remainder,map_sub,coeff_zero_C,sub_self]
  rw [FormalBulk08.Series.map_expan _ zero,FormalBulk08.Series.map_expan _ other]
  apply congrArg FormalBulk08.Series.expan
  apply PowerSeries.ext
  intro e
  simp only [coeff_map]
  exact signed S F R.metals.O R.alloy.B.ratio P facts.1 (R.family.path.levels.blocks j per).branches a M z e

end YM.Integration.WilsonVacuumPreResetIndependentIntegrand
end

