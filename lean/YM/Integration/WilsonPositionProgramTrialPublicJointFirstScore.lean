import YM.Integration.WilsonPositionProgramTrialFirstDiagram
/-! The two signed coefficients of the independently normalized finite tree with its own Wilson action and Haar density. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialPublicJointFirstScore
open Gauge Lattice Wilson XSpace PowerSeries Next.Rank.Normal
open scoped Classical BigOperators
variable {p:XSpace.Period}(T:p.Tree)(G:Gauge)

def score:Bare.Vertices T G:=coeff 1 (Bare.haar T G)+coeff 1 (Bare.interaction T G)

theorem active:coeff 1 (Bare.weight T G)=score T G:=by
  have exp:coeff 1 (Bare.interactionExp T G)=coeff 1 (Bare.interaction T G):=by
    rw [Bare.exponential_formula]
    norm_num [Finset.sum_range_succ]
  rw [Bare.weight,coeff_one_mul,Bare.haar_initial,Bare.exp_starts,mul_one,mul_one,exp]
  rfl

theorem wilson:score T G=coeff 1 (Bare.haar T G)-Taylor.divided (T.basis G) 3
    (Complex.ofRealCLM ∘ T.action):=by
  simp [score,Bare.interaction,sub_eq_add_neg]

theorem original (A:Bare.Series T G):
    constantCoeff (Bare.normalized T G A)=blend (Bare.Q T G) 0 (constantCoeff A) ∧
    coeff 1 (Bare.normalized T G A)=blend (Bare.Q T G) 0 (coeff 1 A+score T G*constantCoeff A)-
      blend (Bare.Q T G) 0 (score T G)*blend (Bare.Q T G) 0 (constantCoeff A):=by
  refine ⟨Bare.leading T A,?_⟩
  have denom:=congrArg (coeff (R:=ℂ) 1) (Bare.normalize_denominator T G A)
  have vac:coeff 1 (Bare.vacuum T G)=blend (Bare.Q T G) 0 (score T G):=by
    rw [Bare.vacuum,Bare.diagram_coeff,mul_one,active]
  rw [coeff_one_mul,Bare.vacuum_start,mul_one,vac,Bare.leading,Bare.diagram_coeff,
    coeff_one_mul,Bare.weight_one,mul_one,active,add_comm (score T G*_)] at denom
  exact eq_sub_of_add_eq denom

end YM.Integration.WilsonPositionProgramTrialPublicJointFirstScore
end
