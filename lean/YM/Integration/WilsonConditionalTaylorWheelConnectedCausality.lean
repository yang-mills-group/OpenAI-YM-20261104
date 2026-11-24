import YM.Integration.WilsonConditionalTaylorWheelConnectedReadout

/-! The genuine connected logarithm of an S-labeled source at a finite
coupling grade uses only lower grades and submasks of that same S. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorWheelConnectedCausality
open Function Filter Lattice Laurent RG Wilson Precision Tree Bloch Exterior
open FormalBulk08 FormalBulk08.Mesa WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue
open WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Wheel.Mark WilsonConditionalTaylorWheelConnectedReadout
open scoped Classical BigOperators
variable {G:Gauge} {I:Type} [DecidableEq I]

theorem product (F Q A B:Mesa.Pot G) (E e:ℕ) (cost:e≤E)
    (prior:∀i≤E,F i=A i) (rest:∀i≤E,Q i=B i):
    Mer.woad F Q e=Mer.woad A B e:=by
  unfold Mer.woad
  apply Finset.sum_congr rfl
  intro a ha
  have occur:a.1+a.2=e:=by simpa using ha
  rw [prior a.1 (by omega),rest a.2 (by omega)]

theorem held (E:ℕ) (A B:Finset I→Mesa.Pot G) (S:Finset I):
    (∀J⊆S,∀i≤E,A J i=B J i)→∀e≤E,logged A S e=logged B S e:=by
  induction S using Finset.strongInductionOn
  case _ S ih=>
    intro old e cost
    by_cases none:S=∅
    · subst S
      rw [logged,dif_pos rfl,logged,dif_pos rfl]
    · rw [logged,dif_neg none,logged,dif_neg none]
      simp only [Pi.sub_apply,Pi.smul_apply,Finset.sum_apply]
      rw [old S (fun _ h=>h) e cost]
      congr 2
      apply Finset.sum_congr rfl
      intro J _
      by_cases w:J⊆S∧J≠S
      · rw [dif_pos w,dif_pos w,Pi.smul_apply,Pi.smul_apply]
        congr 1
        exact product (logged A J) (A (S\J)) (logged B J) (B (S\J)) E e cost
          (ih J (lt_of_le_of_ne w.1 w.2) (fun i hi=>old i (hi.trans w.1))) (old _ Finset.sdiff_subset)
      · rw [dif_neg w,dif_neg w]
end YM.Integration.WilsonConditionalTaylorWheelConnectedCausality
end
