import YM.Integration.WilsonMeasuredPublicEntranceBookedRegulators
/-! Testing all finite fork corners on the purchased compact interpolation table preserves the single signed vacuum-phase correction. The absolute wage is the filed interpolation mass. -/
set_option autoImplicit false
set_option maxHeartbeats 450000
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceTransferProfileMass
open Filter Function Set Finset Extraction Spec RG Source Lattice PhysicalNext.Repeat.Legato
open WilsonMeasuredPublicEntranceBookedSurvey (Press model)
open WilsonSeparatedBranchStencil (bill)
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}{n m:ℕ}{φ:Test n}{r:ℝ}{rp:0<r}{E:Type}[Fintype E]
  {f:ℕ}{ref:E→E4}(A:Press R φ r rp f m ref)

abbrev Data:= (i:A.Entry)→ (model A i).sample→ ℂ

def size:ℝ:=∑i,‖A.coeff i‖*bill (model A i)

def tested (α:(Fin n→Bool)→ℂ)(Z:(Fin n→Bool)→Data A):ℂ:=
  ∑b,α b*WilsonMeasuredPublicEntranceBookedRegulators.collect A (Z b)

def phase (α:(Fin n→Bool)→ℂ)(Gibbs Ear:(Fin n→Bool)→Data A):ℂ:=
  tested A α fun b i a=>Gibbs b i a-Ear b i a

theorem cell {Z X:Data A}{k:ℝ}(sold:∀i a,‖Z i a-X i a‖≤ k):
    ‖WilsonMeasuredPublicEntranceBookedRegulators.collect A Z-WilsonMeasuredPublicEntranceBookedRegulators.collect A X‖≤ size A*k:=by
  classical
  let D:=fun (i:A.Entry)=>
    letI:=(model A i).count
    ∑a:(model A i).sample,(model A i).weight a • (Z i a-X i a)
  have one(i:A.Entry):‖D i‖≤ bill (model A i)*k:=by
    letI:=(model A i).count
    calc
      _ ≤  ∑a:(model A i).sample,‖(model A i).weight a • (Z i a-X i a)‖:=norm_sum_le .. 
      _ ≤  ∑a:(model A i).sample,‖(model A i).weight a‖*k:=
        sum_le_sum fun a _=>by rw [norm_smul];exact mul_le_mul_of_nonneg_left (sold i a) (norm_nonneg _)
      _ = _:=by rw [←Finset.sum_mul];rfl
  have split:WilsonMeasuredPublicEntranceBookedRegulators.collect A Z-WilsonMeasuredPublicEntranceBookedRegulators.collect A X=∑i,A.coeff i*D i:=by
    simp only [D,WilsonMeasuredPublicEntranceBookedRegulators.collect,smul_sub,Finset.sum_sub_distrib,mul_sub]
  rw [split]
  calc
    _ ≤  ∑i,‖A.coeff i*D i‖:=norm_sum_le ..
    _ ≤  ∑i,‖A.coeff i‖*(bill (model A i)*k):=sum_le_sum fun i _=>by
      rw [norm_mul];exact mul_le_mul_of_nonneg_left (one i) (norm_nonneg _)
    _ = _:=by simp only [size,Finset.sum_mul,mul_assoc]

theorem compensated (α:(Fin n→Bool)→ℂ)(Gibbs Ear X:(Fin n→Bool)→Data A)
    (debit:(Fin n→Bool)→ℝ)(sold:∀b i a,‖Ear b i a-X b i a‖≤ debit b):
    ‖tested A α Gibbs-phase A α Gibbs Ear-tested A α X‖≤ 
      ∑b,‖α b‖*(size A*debit b):=by
  have equal:tested A α Gibbs-phase A α Gibbs Ear=tested A α Ear:=by
    simp only [tested,phase,WilsonMeasuredPublicEntranceBookedRegulators.collect,smul_sub,Finset.sum_sub_distrib,mul_sub,sub_sub_cancel]
  rw [equal]
  unfold tested
  rw [←Finset.sum_sub_distrib]
  calc
    _ ≤  ∑b,‖α b*WilsonMeasuredPublicEntranceBookedRegulators.collect A (Ear b)-α b*WilsonMeasuredPublicEntranceBookedRegulators.collect A (X b)‖:=norm_sum_le ..
    _ ≤  _:=sum_le_sum fun b _=>by
      rw [←mul_sub,norm_mul]
      exact mul_le_mul_of_nonneg_left (cell A (sold b)) (norm_nonneg _)

end YM.Integration.WilsonMeasuredPublicEntranceTransferProfileMass
end
