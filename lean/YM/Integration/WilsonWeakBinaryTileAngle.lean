import YM.Next.RANK.LineBox
import YM.Integration.WilsonWeakBinaryGaussianPrice

/-! The original weak net as one of the real angular fields of the funded Wilson post. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonWeakBinaryTileAngle
open Function Filter Finset Lattice Wilson RG Tree Marker Next.Rank Next.Rank.Spindle Stationary Exterior
open Comparison.RG02
open scoped Classical BigOperators Topology
variable {G:Gauge}{n:Side}{o:Site n}{b:ℕ}

def link (p:BudgetPoint)(g:ℝ)(x:Spindle.Space G o b):Stationary.Link G n:=
  (Stationary.arm G n 1).symm (fun e=>g⁻¹ • rollin p o b x (e.1,Exterior.axisEquiv.symm e.2))

theorem collect (p:BudgetPoint)(g:ℝ)(x:Spindle.Space G o b)(e:Edge (Site n)):
    Exterior.collect G (Stationary.arm G n 1 (link p g x)) e=g⁻¹ • rollin p o b x e:=by
  simp only [link,ContinuousLinearEquiv.apply_symm_apply,Exterior.collect]
  change g⁻¹ • rollin p o b x (e.1,Exterior.axisEquiv.symm (Exterior.axisEquiv e.2))=_
  rw [Equiv.symm_apply_apply]

theorem original (p:BudgetPoint)(g:ℝ)(positive:0<g)(x:Spindle.Space G o b):
    let angle:=Stationary.arm G n 1 (link p g x)
    Integral.sample (G:=G) g angle=net p o b x ∧
    (∀e,‖Exterior.collect G angle e‖ ≤ g⁻¹*p.threshold*‖x‖) ∧
    ∀e:Edge (Site n), e ∉ Room o b → Exterior.collect G angle e=0:=by
  intro angle
  refine ⟨?_,?_,?_⟩
  · unfold Integral.sample Precision.represent net
    congr 1
    funext e
    change g • Exterior.collect G angle e=_
    rw [collect,smul_smul,mul_inv_cancel₀ positive.ne',one_smul]
  · intro e
    rw [collect,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr positive),mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr positive.le)
    change ‖if h:e∈Room o b then p.threshold • x ⟨e,h⟩ else 0‖ ≤ _
    split_ifs with h
    · rw [norm_smul,Real.norm_eq_abs,abs_of_pos p.threshold_pos]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm x _) p.threshold_pos.le
    · rw [norm_zero];exact mul_nonneg p.threshold_pos.le (norm_nonneg _)
  · intro e outside
    rw [collect]
    change g⁻¹ • (if h:e∈Room o b then p.threshold • x ⟨e,h⟩ else 0)=0
    simp [outside]

/-- Unit direction budget of the physical comparable-window theorem. -/
theorem admitted (p:BudgetPoint)(g:ℝ)(hg:0<g)(x:Spindle.Space G o b)(small:‖x‖ ≤ 1):
    ∃ z:ℝ,|z| ≤ (p.B:ℝ)^2*p.threshold/g ∧
      ∀e,‖Exterior.collect G (Stationary.arm G n 1 (link p g x)) e‖ ≤ |z|:=by
  let z:=g⁻¹*p.threshold*‖x‖
  have zp:0 ≤ z:=mul_nonneg (mul_nonneg (inv_nonneg.mpr hg.le) p.threshold_pos.le) (norm_nonneg _)
  refine ⟨z,?_,fun e=>((original p g hg x).2.1 e).trans (abs_of_nonneg zp).symm.le⟩
  rw [abs_of_nonneg zp,div_eq_mul_inv]
  have hb:1 ≤ (p.B:ℝ):=by exact_mod_cast p.B_pos
  calc
    z ≤ g⁻¹*p.threshold*1:=mul_le_mul_of_nonneg_left small (mul_nonneg (inv_nonneg.mpr hg.le) p.threshold_pos.le)
    _ ≤ (p.B:ℝ)^2*p.threshold*g⁻¹:=by nlinarith [mul_le_mul_of_nonneg_right (one_le_pow₀ hb (n:=2)) (mul_nonneg p.threshold_pos.le (inv_nonneg.mpr hg.le))]

end YM.Integration.WilsonWeakBinaryTileAngle
end
