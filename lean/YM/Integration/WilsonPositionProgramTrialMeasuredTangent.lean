import YM.Integration.WilsonPositionProgramTrialGroundMeasured
import YM.Pert.First.OneArray

/-! The first coefficient of the nominated finite Wilson programme when the
enrolled input itself is a corrected series. A changed monetary leg is
inserted into the genuine full ground programme on the same finite tree. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialMeasuredTangent
open Finset Lattice RG Wilson Labels Source PhysicalNext.Repeat.Legato PowerSeries
open WilsonThermometerPositionTunedSlope (Columns paid price finite)
open WilsonPositionProgramTrialThermalGrades (frozen)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){I:Type}[Fintype I][LinearOrder I](d:I → ℕ)
local notation "F" i:max  =>  R.family.labels.level (d i)
variable (v : (i : I) → (R.family.labels.level (d i)).Index → PowerSeries ℂ)

def value (k:ℕ)(i:I):(F i).Coeff := fun a => coeff k (v i a)
def move (i j:I):(F j).Coeff := fun a => coeff (if j=i then 1 else 0) (v j a)

private theorem cost (b:Columns R d)(i:I):
    ∏ j, move R d v i j (b j)=coeff 1 (v i (b i))*∏j∈univ.erase i,coeff 0 (v j (b j)) := by
  rw [←mul_prod_erase univ (fun j => move R d v i j (b j)) (mem_univ i)]
  unfold move
  rw [if_pos rfl]
  congr 1
  exact prod_congr rfl (fun j hj => by rw [if_neg (ne_of_mem_erase hj)])

omit [LinearOrder I] in
private theorem entered (u:∀i,(F i).Coeff)(b:Columns R d):
    price R d (frozen R d u) b=PowerSeries.C (∏ j, u j (b j)) := 
  (map_prod PowerSeries.C (fun i => u i (b i)) univ).symm

theorem ground (H:Columns R d → PowerSeries ℂ):
    coeff 0 (paid R d v H)=coeff 0 (paid R d (frozen R d (value R d v 0)) H) := by
  simp only [paid,map_sum,coeff_zero_eq_constantCoeff,price,map_mul,map_prod,
    frozen,constantCoeff_C,value,coeff_zero_eq_constantCoeff]

theorem first (H:Columns R d → PowerSeries ℂ):
    coeff 1 (paid R d v H)=coeff 1 (paid R d (frozen R d (value R d v 0)) H)+
      ∑ i, coeff 0 (paid R d (frozen R d (move R d v i)) H) := by
  rw [WilsonThermometerPositionTunedSlope.first]
  simp only [paid,map_sum,entered,coeff_C_mul]
  rw [sum_add_distrib,Finset.sum_comm (s := univ) (t := univ) (f := fun i (b:Columns R d) => (∏ j, move R d v i j (b j))*coeff 0 (H b))]
  congr 1
  · simp only [price,coeff_zero_eq_constantCoeff,map_prod,value]
  apply sum_congr rfl
  intro b _
  rw [←sum_mul]
  congr 1
  change Pert.First.first (∏ j, v j (b j))=_
  rw [Pert.First.first_product]
  exact sum_congr rfl (fun i _ => by simpa only [Pert.First.first,Pert.First.lead,coeff_zero_eq_constantCoeff] using (cost R d v b i).symm)

theorem original (place:I → Fin 3):
    ∃C:ℝ,0≤C ∧ ∀(v:∀i,(F i).Index → PowerSeries ℂ)(sites:Fin 3 → Cover)
    (P:XSpace.Period)(tree:P.Tree),
    let H := finite R d P (sites∘place) tree
    ‖coeff 1 (paid R d v H)-coeff 1 (paid R d (frozen R d (value R d v 0)) H)‖≤
      C*∑ i, ∏ j, (F j).coeffSize (move R d v i j) := by
  obtain ⟨C,cp,paidGround⟩ := WilsonPositionProgramTrialGroundMeasured.original R d place
  refine ⟨C,cp,fun v sites P tree => ?_⟩
  dsimp only
  rw [first,add_sub_cancel_left,Finset.mul_sum]
  exact (norm_sum_le ..).trans (sum_le_sum (fun i _ => paidGround (move R d v i) sites P tree))

end YM.Integration.WilsonPositionProgramTrialMeasuredTangent
end
