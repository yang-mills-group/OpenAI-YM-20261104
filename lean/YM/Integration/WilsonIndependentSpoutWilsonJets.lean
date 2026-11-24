import YM.Integration.WilsonIndependentSpoutWilsonAction

/-! The bare notebook's nonlinear Wilson coefficients against the literal
top of the independently propagated action, including its thermal shift. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentSpoutWilsonJets
open Lattice WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue RegulatorIR
open RegulatorIR.Binding RegulatorIR.Laplace RegulatorIR.Prim RegulatorIR.Quadratic
open PowerSeries PertExtension.Series.Radial
open WilsonIndependentSpoutWilsonAction
open scoped Classical ContDiff
variable {G:Gauge}{f:Side}

private theorem uncut :
    topW G f=sprig (eWilson (G:=G) (c:=f)) 2 := by
  funext e r
  unfold topW lop
  split_ifs with hr
  · subst r; rw [sprig,shine_dark (by omega : 2+e ≠ 0)]
  · rfl

theorem original (x:Horizon G f)(e:ℕ) :
    MvPolynomial.eval (opening x) (totalR (topW G f e)) =
    2*coeff (2+e) (inscription (priceMap (startO Clocks.flat))
        ((0,1,x):Meadow G Empty × ℝ × Horizon G f)) := by
  let t:=opening x
  let F:TreeVars G f→ℝ:=eWilson
  have hf:ContDiffAt ℝ ∞ F 0:=W_green.of_le (by simp)
  have hg:ContDiffAt ℝ ∞ (fun z:ℝ=>z • t) 0:=contDiffAt_id.smul contDiffAt_const
  have hft:ContDiffAt ℝ ∞ (fun z:ℝ=>F (z • t)) 0:=
    (show ContDiffAt ℝ ∞ F ((0:ℝ) • t) from (zero_smul ℝ t).symm ▸ hf).comp
      (f:=fun z:ℝ=>z • t) 0 hg
  rw [WilsonIndependentSpoutWilsonAction.rays,uncut,sprig,visible_shine,←Blue.jet_apply,rayon]
  have same:(fun v:ℝ=>Clocks.flat.beta v*(eWilson (v • opening x)/2))=
      (fun _:ℝ=>(1/2:ℝ))*(fun z:ℝ=>F (z • t)) := by
    funext v
    simp only [Clocks.flat,Pi.mul_apply,one_mul]
    change F (v • t)/2=(1/2:ℝ)*F (v • t)
    ring
  rw [same,tale_mul contDiffAt_const hft,tale_const,lore hf t,coeff_C_mul,inscription,coeff_mk]
  change _ • _=2*((1/2)*((_ : ℝ)⁻¹*_))
  rw [smul_eq_mul]; ring

end YM.Integration.WilsonIndependentSpoutWilsonJets
