import YM.Integration.WilsonAddressedFiniteGuardHeld
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonAddressedFiniteGuardTrial
open Filter Finset MeasureTheory Lattice Wilson RG Source Labels OPE.Therm Marker QuadraticLocal.Affinity
open PhysicalNext.Repeat.Legato WilsonOriginalAlternativeExtraction MergeProof.Accent
open WilsonAddressedFiniteGuardFields

open WilsonMacroscopicForwardTransfer
open scoped Classical Topology BigOperators
variable {I:Type}[Fintype I][DecidableEq I] {G:Gauge}(R:Run G)(d:I → ℕ)
    {N per K i:ℕ}(live:K ≤ N)(before:i+1 ≤ K)(o:I → Site (R.family.side K per))
    (v:∀a:I,R.family.label (d a))(z:I → ℂ)
local notation "X" => Config G (R.family.side K per)
variable (x:Wallet (WilsonOriginalAlternativeFiniteSource.disks (V:=I))) (s:(Stock.census I).Mode)
def submitted (a:I):R.family.label (d a):=((x a).val*z a) • v a
local notation "ξ" => submitted R d v z x
def printed (U:X):ℂ:=
  ∏a∈s.val,∑l,WilsonPositionProgramReportedField.entire R (d a) K (N,per) (ξ a) l*
    WilsonPositionProgramBlockedTrialFiling.atomAt R (d a) N per K (o a) l U

include live in
theorem original:
    printed R d (N:=N) o v z x s=face (WilsonAddressedFiniteGuardFields.raw R d N per K o ξ) s.val ∧
    WilsonOriginalAlternativeTrialSource.mode R d N per K o v z x s=
      face (WilsonAddressedFiniteGuardFields.guarded R d N per K o ξ) s.val:=by
  constructor
  · funext U
    apply Finset.prod_congr rfl
    intro a _
    exact (WilsonAddressedFiniteGuardFields.source R d N per K o ξ live a U).2.symm
  · funext U
    apply Finset.prod_congr rfl
    intro a _
    change (x a).val*(z a*_)=
      (Extra.Histories.part (R.family.localSection (d a)) (o a) (R.family.path.rep N per K) U)
        (((x a).val*z a) • v a)
    rw [LinearMap.map_smul,smul_eq_mul,mul_assoc]

include before live in
theorem returned (W:Config G (R.family.side i per)):
    let read:=fun U:(X → ℂ)=>actualTransport R.family (N:=N) U ((Nat.le_succ i).trans before) W
    read (printed R d (N:=N) o v z x s)-read (WilsonOriginalAlternativeTrialSource.mode R d N per K o v z x s)=
      read (WilsonAddressedFiniteGuardFields.gap R d N per K o ξ s.val):=by
  intro read
  let old:=WilsonAddressedFiniteGuardFields.guarded R d N per K o ξ
  let new₀:=WilsonAddressedFiniteGuardFields.raw R d N per K o ξ
  let B:=WilsonAddressedFiniteGuardFields.cap R d N per K ξ
  let price:=∏a∈s.val,B a
  let law:=WilsonMacroscopicRichFlatPosteriorLaw.law R N per before W
  letI:IsProbabilityMeasure (scene R.family.path N per K):=probability R.makes.wilson live
  letI:IsProbabilityMeasure law:=WilsonMacroscopicRichFlatPosteriorLaw.prob R before live W
  have solve (P:I → X → ℂ)(borel:∀a,Measurable (P a))(paid:∀a U,‖P a U‖ ≤ B a):
      read (face P s.val)=(∫U,face P s.val U ∂law) ∧ Integrable (face P s.val) law:=by
    have measurable:Measurable (face P s.val):=Finset.measurable_prod _ fun a _=>borel a
    have gross (U:X):‖face P s.val U‖ ≤ price:=by
      rw [face,norm_prod]
      exact Finset.prod_le_prod (fun _ _=>norm_nonneg _) (fun a _=>paid a U)
    have admitted (ν:Measure X)[IsProbabilityMeasure ν]:Integrable (face P s.val) ν:=
      Integrable.of_bound measurable.aestronglyMeasurable price (ae_of_all _ gross)
    refine ⟨?_,admitted law⟩
    exact (congrFun (WilsonSeparatedOriginalPosteriorTransport.realized (C:=R.family) (N:=N)
      (p:=per) R.makes live ((Nat.le_succ i).trans before) (face P s.val) (admitted _)).symm W).trans
        (WilsonMacroscopicRichFlatPosteriorLaw.reading R before live W (face P s.val) (admitted _))
  have h:=WilsonAddressedFiniteGuardFields.unary R d N per K o ξ
  have left:=solve new₀ (fun a=>(h a).2.1) (fun a U=>((h a).2.2 U).2)
  have right:=solve old (fun a=>(h a).1) (fun a U=>((h a).2.2 U).1)
  have pass:=original R d live o v z x s
  have due:=WilsonAddressedFiniteGuardHeld.original R d live before o ξ s.val W
  rw [pass.1,pass.2,left.1,right.1]
  exact (integral_sub left.2 right.2).symm.trans due.1.symm

end YM.Integration.WilsonAddressedFiniteGuardTrial
end
