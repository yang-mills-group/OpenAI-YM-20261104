import YM.Integration.WilsonIndependentCollarDatedProbeSalary
import YM.Integration.WilsonIndependentCollarDatedUpperBasis

/-! Multiply the actual fixed-cutoff canonical dose of each occurring label
by the paid angular test. The tested dose may vary with the original
regulators. The geometric bound has no auxiliary-page cardinality. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentCollarOrbitalBasisPayment
open Finset Function Lattice RG Wilson Marker Multi QuadraticLocal QuadraticLocal.Earn PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Embroider
open WilsonIndependentCollarOriginalDose (weight axisFee)
open WilsonThermometerDeclaredSeeds WilsonReceivedCanonicalVerseBasis
open WilsonIndependentCollarOrbitalPeg (ink)
open WilsonReceivedDepositedOrbitalNamedWage (wages)
open WilsonOriginalMixedBlockRows (room)
open scoped Classical BigOperators

variable {G:Gauge}{I:Type}[Fintype I][DecidableEq I]{side:Side}{n:ℕ}{D k:Fin n→ℕ}{P:Passport side (Fin n)}
  (R:Run G)(B:I→Binder P (Stock.census (Fin n)))(N per K:ℕ)(top:K ≤ N)(v:(l:Fin n)→R.family.label (k l))
  (target:(Stock.census (Fin n)).Mode)(g size:ℝ)(positive:0 < g)(small:g ≤ 1)(span:0 ≤ size)
abbrev Choices (R:Run G)(k:Fin n→ℕ)(s:Finset (Fin n)) := (j:s)→Choice R k j
local notation "Seeds" => Choices R k target.val

include top positive small span in
theorem original (x:Seeds→Affinity.Wallet (room (Fin n)))(paint:Seeds→Case D)(C:Fin n→ℝ)(Cpos:∀v,0≤C v)
    (cap:∀(a:Seeds)(j:Fin n),j∈target.val → ‖(x a j).val‖*‖paint a j‖≤C j):
    (∑a:Seeds, (∏j:target.val,weight R k N per K v j (a j) g size) *
      ∑s:Finset I,‖wages B (x a) target s‖ * ∏z∈s,‖ink (paint a) (B z).mode.val‖) ≤
      (∏j:target.val,axisFee R k v j*(size/g)^(k j)) *
      ((2:ℝ)^(Fintype.card I) * ∏j∈target.val,C j) := by
  let dose:Seeds→ℝ:=fun a=>∏j:target.val,weight R k N per K v j (a j) g size
  let fare:ℝ:=(2:ℝ)^(Fintype.card I)*∏j∈target.val,C j
  have prices(a:Seeds):0≤dose a:=prod_nonneg fun _ _=>mul_nonneg
    (mul_nonneg (norm_nonneg _) (pow_nonneg (inv_nonneg.mpr positive.le) _)) (pow_nonneg span _)
  have component(a:Seeds): (∑s:Finset I,‖wages B (x a) target s‖ * ∏z∈s,‖ink (paint a) (B z).mode.val‖) ≤ fare :=
    (WilsonIndependentCollarOrbitalDose.original B (x a) (paint a) target).trans
      (mul_le_mul_of_nonneg_left (prod_le_prod (fun _ _=>mul_nonneg (norm_nonneg _) (norm_nonneg _)) (cap a)) (by positivity))
  have non:0≤fare:=mul_nonneg (by positivity) (prod_nonneg (fun j _=>Cpos j))
  calc
    _ ≤ ∑a:Seeds,dose a*fare:=sum_le_sum fun a _=>mul_le_mul_of_nonneg_left (component a) (prices a)
    _ = (∑a:Seeds,dose a)*fare:=(Finset.sum_mul ..).symm
    _ ≤ _ :=mul_le_mul_of_nonneg_right (WilsonIndependentCollarOriginalDose.family R k N per K top v target.val
      g size positive small span) non

end YM.Integration.WilsonIndependentCollarOrbitalBasisPayment
end
