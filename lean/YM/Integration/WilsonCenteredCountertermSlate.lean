import YM.Integration.WilsonCenteredSingletonFiled

/-! One original physical coefficient for the product of two independently
placed children less the entire finite, complex centre counterterm. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredCountertermSlate
open Finset Function Lattice RG Wilson Marker QuadraticLocal Ac Source Labels Push.Local
open Planned.GuardedAtom Extra.Trajectories WilsonCenteredFiledAtoms WilsonCenteredLampCapture
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {V X ι : Type} [DecidableEq V] [Fintype V]
    {P : Rep G n} {o : V→Site n} {R : Census V} {d : ℕ} {F : Frame G d}

def fare (p : BudgetPoint) (S : SectionData F) (Y : Hol G) (w : V→ℝ)
    (a b : V) (s : R.Mode) (counter : Finset V) (z : V→ℂ) (Z : Support n) (rad : ℕ) (E κ η μ : ℝ) :=
  (WilsonCenteredAbsoluteGallery.fare p S Y w a b a s Z rad E κ η μ+
    WilsonCenteredSingletonFiled.fare p S Y w (R.fire a) 1 Z rad E κ η μ)+
    ∑c∈counter,WilsonCenteredSingletonFiled.fare p S Y w (R.fire c) (z c) Z rad E κ η μ

theorem original (A : Gallery X ι o P R) (x : X) (a b : V) (s : R.Mode)
    (apart : a≠b) (pair : s.val={a,b}) (counter : Finset V) (z : V→ℂ)
    (w : V→ℝ) (hw : ∀ i,0<w i) {E κ η σ C Λ δ μ : ℝ}
    (regular : A.E.Paid w P.p.B (P.p.supportExponent+2) E)
    (hard : A.K.Paid w P.p.B P.p.supportExponent κ)
    (hk : 0<κ) (hv : 0≤η) (room : hitWidth P.p*η≤1) (width : 0≤P.p.supportExponent)
    (law : P.Lawful σ C Λ δ η) (K : Guard.Keeper P.p P.activities) (Z : Support n)
    (y : Site n) (center : y∈Z) (za : o a∈Z) (zb : o b∈Z) (zc : ∀ c∈counter,o c∈Z)
    (rad : ℕ) (na : separation (o a) y≤rad) (nb : separation (o b) y≤rad)
    (nc : ∀ c∈counter,separation (o c) y≤rad)
    (S : SectionData F) (Y : Hol G) (reader : Readable Y S P.p n μ) :
    Store P S Y y κ (fare P.p S Y w a b s counter z Z rad E κ η μ)
      (fun U=>(A.density x U).part s-∑c∈counter,z c*(A.density x U).part (R.fire c)) := by
  have pairMinus:=WilsonCenteredAbsoluteGallery.original A x a b a s apart pair w hw regular hard hk hv room width
    law K Z y center za zb za rad na nb na S Y reader
  have first:=WilsonCenteredSingletonFiled.original A x a 1 w hw regular hard hk hv room width
    law K Z y center za rad na S Y reader
  have product:=add law hk pairMinus first
  let cost (c : V) := WilsonCenteredSingletonFiled.fare P.p S Y w (R.fire c) (z c) Z rad E κ η μ
  have slate (T : Finset V) (subset : T⊆counter) :
      Store P S Y y κ (∑c∈T,cost c) (fun U=>∑c∈T,z c*(A.density x U).part (R.fire c)) := by
    induction T using Finset.induction with
    | empty =>
      obtain ⟨Q,form,bill,val⟩:=empty (P:=P) S Y y hk
      exact ⟨Q,form,by simpa only [sum_empty] using bill,fun U=>by simpa only [Pi.zero_apply,sum_empty] using val U⟩
    | insert c t fresh ih =>
      have frame:=insert_subset_iff.mp subset
      have slot:=WilsonCenteredSingletonFiled.original A x c (z c) w hw regular hard hk hv room width
        law K Z y center (zc c frame.1) rad (nc c frame.1) S Y reader
      obtain ⟨Q,form,bill,val⟩:=add law hk slot (ih frame.2)
      refine ⟨Q,form,?_,fun U=>?_⟩
      · simpa only [sum_insert fresh] using bill
      rw [val]
      simp only [Pi.add_apply,sum_insert fresh]
  obtain ⟨Q,form,bill,val⟩:=sub law product (slate counter Subset.rfl)
  refine ⟨Q,form,bill,fun U=>?_⟩
  rw [val]
  simp only [Pi.add_apply,Pi.sub_apply,one_mul,sub_add_cancel]

end YM.Integration.WilsonCenteredCountertermSlate
