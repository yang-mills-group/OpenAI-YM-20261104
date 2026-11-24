import YM.Integration.WilsonIndependentNotebookConstantSeat
import YM.Integration.WilsonIndependentConditionedBankRawUnits

/-! The priced original cutoff row in the complete reported/independent Section. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentNotebookFundedRow
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

theorem extensive (e:ℕ)(im:Bool)(w:F.Coeff)(A:Alma F→ℝ){τ:ℝ}(pos:0≤τ):
    charge e (issue F im (τ • w)) A=τ*charge e (issue F im w) A:=by
  rw [exact_charge,exact_charge,mul_left_comm τ]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have factor:part im ((τ • w) i)=τ*part im (w i):=by
    cases im with
    | false => exact Complex.smul_re ..
    | true => exact Complex.smul_im ..
  rw [factor,abs_mul,abs_of_nonneg pos]
  ring

theorem original (R:Run G)(W:Initialize G)(survey:Bool)(fit:d<D)(capacity:d≤k)(e u:ℕ):
    let F:=R.family.labels.level d
    let T:=sectionAt R W survey d
    let a:=R.family.S.a
    ∃(A:Alma F→ℝ)(M:ℝ),(∀i,0≤A i) ∧ 0≤M ∧ ∀{j f K N p target:ℕ}
      (before:j ≤ f)(up:f ≤ K)(live:K ≤ N){η:ℝ}
      (S:(R.family.label d)≃ₗ[ℂ]R.family.label d)(Y:R.family.label d){salary:ℝ}
      (_paid:Cash (R:=R) d j f K N p target before up live η S Y salary)
      (arm:Arm R d N p f K)(_same:arm.w=S.symm (fitted R d j N p Y))(t:ℂ)(im:Bool),
      let δ:=a K/a f
      let z:=row R d K N p t (coords R arm)
      let cost:=(e+1:ℕ)*M*(home R d j f η t salary*δ^(-η))
      let c:=issue F im ((δ^d) • z)
      On k (Shrine (plate T fit) c) ∧
        Shrine (plate T fit) c=(δ^d) • Shrine (plate T fit) (issue F im z) ∧
        charge e c A=δ^d*charge e (issue F im z) A ∧
        charge e c A≤cost ∧ ∀l r,l≤e→Fruit 0 1 u ((Shrine (plate T fit) c).2 l r) cost:=by
  intro F T a
  obtain ⟨A,non,grant⟩:=WilsonIndependentMatchedFiledIncome.named R W survey d fit capacity e u
  let M:=∑i:F.Index,A (seat F i)
  have pos:0≤M:=sum_nonneg fun _ _=>non _
  have hi i:A (seat F i)≤M:=single_le_sum (f:=fun l=>A (seat F l)) (fun _ _=>non _) (mem_univ i)
  refine ⟨A,M,non,pos,?_⟩
  intro j f K N p target before up live η S Y salary paid arm same t im δ z cost c
  have pn:0≤δ^d:=pow_nonneg (div_nonneg (R.family.S.a_pos K).le (R.family.S.a_pos f).le) _
  have cap:=WilsonIndependentConditionedBankRawUnits.original R before up live S Y paid arm same t
  change δ^d*F.coeffSize z≤_ at cap
  have hom:=extensive e im z A pn
  have bill:charge e c A≤cost:=calc
    _=δ^d*charge e (issue F im z) A:=hom
    _≤δ^d*((e+1:ℕ)*M*F.coeffSize z):=mul_le_mul_of_nonneg_left (charged e im z A M pos hi) pn
    _=((e+1:ℕ)*M)*(δ^d*F.coeffSize z):=by ring
    _≤cost:=mul_le_mul_of_nonneg_left cap (mul_nonneg (by positivity) pos)
  exact ⟨(grant c).1,scale T fit im z δ,hom,bill,fun l r hl=>((grant c).2.2 l r hl).more bill⟩

end YM.Integration.WilsonIndependentNotebookFundedRow
