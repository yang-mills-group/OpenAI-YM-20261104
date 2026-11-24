import YM.Integration.WilsonIndependentConditionalHeldGaussian
import YM.WilsonCoeffUV.Emit.GaussianConvention
import YM.WilsonCoeffUV.Step.Source

/-! The occupied derivative of a normalized genuine conditional on the elected Wilson tree. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentConditionalInsertion
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Convention RegulatorIR RegulatorIR.Diagram
open WilsonIndependentConditionalHeldGaussian PertExtension PertExtension.GaussianScore MeasureTheory PowerSeries
open Lattice FreeResolvent Metric RG Wilson Tree Precision Matrix Exterior
open scoped Classical BigOperators MatrixOrder
variable {I J:Type} [Fintype I] [Fintype J] [DecidableEq I]
    {C:Matrix I I ℝ} (h:C.PosDef) (μ:Measure (Lawn I))
    [μ.HasTemperateGrowth] [μ.IsAddRightInvariant] [NeZero μ]

def read (b:J→ℝ)(p:Ink (I⊕J)):PowerSeries ℝ:=
  burn (law h) (noise (tooth (X:=I))) μ p (held b)

omit [Fintype J] in
private theorem inverse : Gaussian.bond (law h) (tooth (X:=I))=C⁻¹ :=by
  classical
  have hc:C*C⁻¹=1:=Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr h.det_pos.ne')
  funext i j
  rw [Gaussian.bond_cross,Gaussian.bond,inverse_tooth h hc]

theorem reading (b:J→ℝ)(p:Ink (I⊕J)):
    read h μ b p=PowerSeries.map (emphasis b).toRingHom (Wick J C⁻¹ p):=by
  rw [read,WilsonIndependentConditionalHeldGaussian.original,inverse]

/-- The auxiliary marker is independent of the coupling already present in both complete inputs. -/
def tilt (b:J→ℝ)(vac src:Ink (I⊕J)):PowerSeries (PowerSeries ℝ):=
  PowerSeries.mk fun j=>PowerSeries.C (j.factorial:ℝ)⁻¹ * read h μ b (vac*src^j)

omit [Fintype J] [μ.HasTemperateGrowth] [μ.IsAddRightInvariant] [NeZero μ] in
theorem zero (b:J→ℝ)(vac src:Ink (I⊕J)):
    coeff 0 (tilt h μ b vac src)=read h μ b vac:=by simp [tilt]
omit [Fintype J] [μ.HasTemperateGrowth] [μ.IsAddRightInvariant] [NeZero μ] in
theorem one (b:J→ℝ)(vac src:Ink (I⊕J)):
    coeff 1 (tilt h μ b vac src)=read h μ b (vac*src):=by simp [tilt]

variable {G:Gauge}{c f:Side} (S:StepData c f)(F:Forest S.ratio)(H:FaceRow)
  (Q:Matrix (Body 1 f) (Body 1 c) ℝ)
  (hf:(treeMatrix G S F H).PosDef)
  (ν:Measure (Lawn (Active G F))) [ν.HasTemperateGrowth] [ν.IsAddRightInvariant] [NeZero ν]

theorem original {Ñ:ChartRatio G}{P w:PChart G f}{l:ℕ} (p:shellK 2 P)(ratio:LocalRatio Ñ)
    (oper:shellK l w)(branch:S.patch.Branches S.kernel G)(sym:(H.acts f).transpose=H.acts f)
    (pure:∀ i,Pure (P i))(wpure:∀ i,Pure (w i))(b:Woods G c→ℝ):
    let density:=raiseE (shot S F Q Ñ P)
    let inlet:=loom (camSlice G S F (extractV G S F Q)) (flash w)
    let Z:=tilt hf ν b density inlet
    constantCoeff (coeff 0 Z)=1 ∧ ∀ r:PowerSeries ℝ, coeff 1 Z=coeff 0 Z*r ↔
      r=PowerSeries.map (emphasis b).toRingHom (flash (reed S F H Q Ñ P l w)) :=by
  intro density inlet Z
  have cov: treeInverse G S F H 0=(treeMatrix G S F H)⁻¹:=by simp [treeInverse,resolve]
  have vac:coeff 0 Z = PowerSeries.map (emphasis b).toRingHom (inside S F H Q Ñ P):=by
    rw [show coeff 0 Z=read hf ν b density from zero ..,reading]
    rw [inside,cov]
  have mass:constantCoeff (coeff 0 Z)=1:=by
    rw [←coeff_zero_eq_constantCoeff_apply,vac,coeff_map,coeff_zero_eq_constantCoeff_apply,inside_mass S F H Q ratio,map_one]
  have live:coeff 1 Z=coeff 0 Z*PowerSeries.map (emphasis b).toRingHom (flash (reed S F H Q Ñ P l w)):=by
    rw [show coeff 1 Z=read hf ν b (density*inlet) from one ..,reading,vac,←map_mul,
      ←inside_reed S F H Q l p ratio oper branch sym pure wpure,insideMark,cov]
  refine ⟨mass,fun r=>⟨fun hr=>?_,fun h=>h ▸ live⟩⟩
  apply mul_left_cancel₀ _ (hr.symm.trans live)
  intro h0
  rw [h0,map_zero] at mass
  exact zero_ne_one mass

end YM.Integration.WilsonIndependentConditionalInsertion
