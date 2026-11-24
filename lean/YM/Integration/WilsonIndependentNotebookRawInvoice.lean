import YM.Integration.WilsonIndependentNotebookFundedRow

/-! The literal original cutoff issue on the shelves already chosen by the opening. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentNotebookRawInvoice
open Finset Lattice RG Wilson Source Labels XSpace XSpace.Rose XSpace.Cirrus
open PhysicalNext.Repeat.Legato WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Embroider
open WilsonCoeffUV.Shard WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Fountain
open WilsonIndependentNotebookConstantSeat (seat part issue exact_charge charged scale)
open WilsonIndependentMatchedFiledIncome (plate charge)
open WilsonIndependentMatchedNamedPair (sectionAt)
open WilsonAddressedTrialPivotUnits (row)
open WilsonIndependentConditionedBankRawUnits (home)
open WilsonReflectedMixedSharpAxis (Cash)
open WilsonReflectedFundedHearing (Arm)
open WilsonReflectedPublicGuardedMotion (coords)
open WilsonMeasuredPublicEntranceGridDebit (fitted)
open scoped BigOperators Classical
variable {G:Gauge}{d D k:ℕ}{F:Labels.Frame G d}

theorem original (R:Run G)(W:Initialize G)(survey:Bool)(fit:d<D)(e:ℕ)
    (A:Alma (R.family.labels.level d)→ℝ)(non:∀i,0≤A i)
    {j f K N p target:ℕ}(before:j ≤ f)(up:f ≤ K)(live:K ≤ N){η:ℝ}
    (S:(R.family.label d)≃ₗ[ℂ]R.family.label d)(Y:R.family.label d){salary:ℝ}
    (paid:Cash (R:=R) d j f K N p target before up live η S Y salary)
    (arm:Arm R d N p f K)(same:arm.w=S.symm (fitted R d j N p Y))(t:ℂ)(im:Bool):
    let F:=R.family.labels.level d
    let δ:=R.family.S.a K/R.family.S.a f
    let z:=row R d K N p t (coords R arm)
    let M:=∑i:F.Index,A (seat F i)
    let c:=issue F im ((δ^d) • z)
    let T:=sectionAt R W survey d
    Shrine (plate T fit) c=(δ^d) • Shrine (plate T fit) (issue F im z) ∧
      charge e c A=δ^d*charge e (issue F im z) A ∧
      charge e c A≤(e+1:ℕ)*M*(home R d j f η t salary*δ^(-η)):=by
  intro F δ z M c T
  have pos:0≤M:=sum_nonneg fun _ _=>non _
  have hi i:A (seat F i)≤M:=single_le_sum (f:=fun l=>A (seat F l)) (fun _ _=>non _) (mem_univ i)
  have pn:0≤δ^d:=pow_nonneg (div_nonneg (R.family.S.a_pos K).le (R.family.S.a_pos f).le) _
  have cap:=WilsonIndependentConditionedBankRawUnits.original R before up live S Y paid arm same t
  change δ^d*F.coeffSize z≤_ at cap
  have hom:=WilsonIndependentNotebookFundedRow.extensive e im z A pn
  refine ⟨scale T fit im z δ,hom,?_⟩
  calc
    _=δ^d*charge e (issue F im z) A:=hom
    _≤δ^d*((e+1:ℕ)*M*F.coeffSize z):=mul_le_mul_of_nonneg_left (charged e im z A M pos hi) pn
    _=((e+1:ℕ)*M)*(δ^d*F.coeffSize z):=by ring
    _≤_:=mul_le_mul_of_nonneg_left cap (mul_nonneg (by positivity) pos)

end YM.Integration.WilsonIndependentNotebookRawInvoice
