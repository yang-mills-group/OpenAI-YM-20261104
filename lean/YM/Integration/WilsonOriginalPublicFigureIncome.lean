import YM.Integration.WilsonOriginalPublicTrialFigure

/-! Total variation of the actual coefficients of a measured fixed-station source,
before either physical regulator and including all the inverse powers carried by the stencils. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 600000
namespace YM.Integration.WilsonOriginalPublicFigureIncome
open Finset Wilson RG Labels Lattice Extra.Histories PhysicalNext PhysicalNext.Repeat.Legato Pert.Asymptotics
open WilsonOriginalMicroscopicGuardedPageSchool WilsonOriginalPublicTrialInput WilsonOriginalPublicTrialFigure
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)(d:ℕ)
local notation "F" => R.family.labels.level d

def height : ℕ:=univ.sup fun i:(F).Index=>((F).grades i).2
def scale (K:ℕ):ℝ:=max 1 (Real.sqrt (2*R.family.path.levels.clock.hatBeta K))

theorem pole (N per K:ℕ)(live:K≤N)(i:(F).Index):
    abs ((regulatorRun R.family N per K ^ ((F).grades i).2)⁻¹) ≤ scale R K ^height R d:=by
  have bound: R.family.path.β N per K ≤ 2*R.family.path.levels.clock.hatBeta K:=
    (R.makes.wilson.represents N per K live).band.2
  have hh:((F).grades i).2≤height R d:=Finset.le_sup (f:=fun i:(F).Index=>((F).grades i).2) (mem_univ i)
  rw [←inv_pow,regulatorRun,inv_inv,abs_of_nonneg (pow_nonneg (Real.sqrt_nonneg _) _)]
  exact (pow_le_pow_left₀ (Real.sqrt_nonneg _) ((Real.sqrt_le_sqrt bound).trans (le_max_right ..)) _).trans
    (pow_le_pow_right₀ (le_max_left ..) hh)

theorem letter {I:Type}[Fintype I][LinearOrder I](t:I→ℕ)(N per K:ℕ)(live:K≤N)
    (v:∀i,(R.family.labels.level (t i)).Coeff)(b:∀i,(R.family.labels.level (t i)).Index):
    ‖WilsonOriginalPublicTrialFigure.weight R t (regulatorRun R.family N per K) v b‖ ≤
      ∏i,(R.family.labels.level (t i)).coeffSize (v i)*scale R K^height R (t i):=by
  rw [WilsonOriginalPublicTrialFigure.weight,norm_prod]
  refine prod_le_prod (fun _ _=>norm_nonneg _) (fun i _=>?_ )
  rw [WilsonOriginalPublicTrialFigure.amount,norm_mul,Complex.norm_real,Real.norm_eq_abs]
  have one:‖v i (b i)‖ ≤ (R.family.labels.level (t i)).coeffSize (v i):=
    Finset.single_le_sum (f:=fun a=>‖v i a‖) (fun a _=>norm_nonneg _) (mem_univ (b i))
  exact mul_le_mul one (pole R (t i) N per K live (b i)) (abs_nonneg _) ((norm_nonneg _).trans one)
variable {I:Type}[Fintype I][LinearOrder I](grades j:Fin 3→ℕ)(K target:ℕ)(η:ℝ)(M:Fin 3→ℝ)
    (Y:∀a:Fin 3,ℕ×ℕ→R.family.label (grades a))(before:∀a,j a≤K)
    (registered:Indexed R grades j target η M Y)(child:I→Fin 3)
def bill :=Fintype.card (∀i,(R.family.labels.level (grades (child i))).Index)*(∏i,(2*scale R K)^height R (grades (child i))*salary R grades j K η M (child i))

theorem original (N per:ℕ)(live:K<N):
    let v:=vector R grades j K target η M Y before registered N per
    ∑a,‖WilsonOriginalPublicTrialFigure.weight R (grades ∘ child) (regulatorRun R.family N per K) (fun i=>v (child i)) a‖≤
      bill R grades j K η M child:=by
  intro v
  let fit:=fitted R grades j K target η M Y before registered N per
  have paid:=(WilsonOriginalPublicTrialInput.original R grades j K target η M Y before registered N per live).1
  rw [bill,←nsmul_eq_mul,←Finset.card_univ,←Finset.sum_const]
  apply sum_le_sum
  intro b _
  refine (letter R (grades ∘ child) N per K live.le (fun i=>v (child i)) b).trans ?_
  apply prod_le_prod (fun i _=>mul_nonneg (sum_nonneg fun _ _=>norm_nonneg _)
    (pow_nonneg (zero_le_one.trans (le_max_left ..)) _))
  intro i _
  let t:=grades (child i)
  have hf:(R.family.labels.level t).coeffSize (v (child i))≤ 2^height R t*salary R grades j K η M (child i):=by
    simp only [v,vector,if_pos live]
    exact (WilsonPositionProgramReportedField.purchased R t K (N,per) live.le (fit (child i))).trans
      (mul_le_mul_of_nonneg_left (paid (child i)).2 (by positivity))
  have sc:(0:ℝ) ≤ scale R K ^height R t:=pow_nonneg (zero_le_one.trans (le_max_left ..)) _
  calc
    _ ≤ _ := mul_le_mul_of_nonneg_right hf sc
    _ = _ := by change (2^height R t * salary R grades j K η M (child i))*_=
                              (2*scale R K)^height R t*salary R grades j K η M (child i)
                rw [mul_pow];ring


end YM.Integration.WilsonOriginalPublicFigureIncome
end
