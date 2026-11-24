import YM.Integration.WilsonCenteredHardFiled
import YM.Integration.WilsonCenteredCaptureLampRoster

/-! A signed regular–hard cofactor pays the original hard exponent on its
named owner. The extra exponent belongs to the submitted regular query. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredCrossWallet
open Finset RG Lattice Wilson Marker QuadraticLocal Ac Planned.GuardedAtom Push.Local Push.AbsoluteSums
open Corona
open WilsonCenteredKeptOwners WilsonCenteredHardWallet WilsonCenteredOriginalCaptureOwner WilsonCenteredCaptureSlots
open WilsonCenteredCaptureLampRoster
open scoped BigOperators Classical
variable {G : Gauge} {n : Side} {V X ι : Type} [DecidableEq V] {R : Census V} {o : V→Site n}
    {P : Rep G n} (L : Lamps X ι G P.p o R) (H : Hard X P.p P.activities.forced P.activities.K o R)
    (a b : V) (Z : Support n)

abbrev Lots := Row L (R.fire a)×ℕ

def ground (z : Lots L a) := Z∪L.ground z.1.val
def owner (z : Lots L a) : Finset ℕ := {z.2}
def word (x : X) (z : Lots L a) (U : Config G n) :=
  (L.frame z.1.val x U).part (R.fire a)*(H.hard x z.2 U).part (R.fire b)

theorem invoice (w : V→ℝ) (hw : ∀ i,0<w i) {E κ : ℝ}
    (width : 0≤P.p.supportExponent+2) (regular : L.Paid w P.p.B (P.p.supportExponent+2) E)
    (hard : H.Paid w P.p.B P.p.supportExponent κ) (za : o a∈Z) (zb : o b∈Z) :
    ∃ e : Lots L a→ℝ,(∀ z,0≤e z) ∧
      (∀ z,e z≠0→∀ j∈owner L a z,∃ u∈ground L a Z z,u∈Push.Local.patch P.activities j) ∧
      (∀ z x U,‖word L H a b x z U‖≤e z) ∧
      SumBudget (fun z=>reservedMass P.p (ground L a Z z) (salary P (owner L a) e z))
        ((Real.exp ((P.p.supportExponent+2)*coverNumber P.p.B Z)*((w a)⁻¹*E))*((w b)⁻¹*κ)) := by
  obtain ⟨l,lp,cap,duel⟩:=WilsonCenteredCaptureLampRoster.single L (R.fire a) a (mem_singleton_self _) w hw width regular Z za
  obtain ⟨h,hp,touch,char,duer⟩:=WilsonCenteredHardWallet.original H w hw (R.fire b) b (mem_singleton_self _) hard
  let e (z : Lots L a):=l z.1*h z.2
  refine ⟨e,fun z=>mul_nonneg (lp _) (hp _),fun z live j hj=>?_,fun z x U=>?_,?_⟩
  · have eq : j=z.2:=mem_singleton.mp hj
    exact ⟨o b,mem_union_left _ zb,eq.symm ▸ touch _ (right_ne_zero_of_mul live)⟩
  · have given := cap z.1 x
    have clip (W) (healthy : Healthy P.p.threshold (L.ground z.1.val) W) :
        ‖L.nominal x z.1.val W‖≤ l z.1:=given.2 W healthy [] (Nat.zero_le _) (by simp)
    have first : ‖L.light x z.1.val U‖≤l z.1 := by
      unfold Lamps.light
      split
      next hc=>rw [L.pure _ _ _ hc];exact clip 1 (Next.Foundations.one_healthy _ _ P.p.threshold_pos.le)
      next=>by_cases hh : Healthy P.p.threshold (L.ground z.1.val) U
            · rw [masked_eq _ _ _ _ hh];exact clip U hh
            rw [masked_ne _ _ _ _ hh,norm_zero];exact lp _
    have value:=(mul_le_mul first (char z.2 x U) (norm_nonneg ((H.hard x z.2 U).part (R.fire b))) (lp z.1))
    simpa only [word,Lamps.frame,Poly.part_send,z.1.property,if_true,if_pos rfl,norm_mul,e] using value
  have paid:=budget_prod duel duer
  simp only [Poly.solo_toll] at paid
  convert paid using 1
  ext z
  simp only [reservedMass,salary,owner,sum_singleton,ground,e]
  ring

end YM.Integration.WilsonCenteredCrossWallet
