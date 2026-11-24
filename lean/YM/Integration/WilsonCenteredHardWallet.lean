import YM.Integration.WilsonCenteredOwnerIntake
import YM.Integration.WilsonCenteredHardEnvelope

/-! Before-field wallets for a complete deposited hard mode or for two
distinct hard owners. Each named support uses the native hard exponent. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredHardWallet
open Finset Function RG Lattice Wilson Marker QuadraticLocal Ac Push.Local
open Push.AbsoluteSums
open WilsonCenteredKeptOwners WilsonCenteredOriginalCaptureOwner
open scoped BigOperators Classical
variable {G : Gauge} {n : Side} {V X : Type} [DecidableEq V] {R : Census V} {o : V→Site n}
    {P : Rep G n} (H : Hard X P.p P.activities.forced P.activities.K o R) (w : V→ℝ) (hw : ∀ i,0<w i)

include hw
theorem original (s : R.Mode) (v : V) (member : v∈s.val) {α κ : ℝ} (wallet : H.Paid w P.p.B α κ) :
    ∃ e : ℕ→ℝ,(∀ i,0≤e i) ∧ (∀ i,e i≠0→ o v∈Push.Local.patch P.activities i) ∧
      (∀ i x U,‖(H.hard x i U).part s‖≤e i) ∧
      SumBudget (fun i=>Real.exp (α*coverNumber P.p.B (Push.Local.patch P.activities i))*e i) ((Poly.toll w s)⁻¹*κ) := by
  obtain ⟨g,covers,spent⟩:=wallet.wages
  let t := (Poly.toll w s)⁻¹
  let e i := if o v∈Push.Local.patch P.activities i then t*Poly.price w (g i) else 0
  have ht : 0<t:=inv_pos.mpr (Poly.worth hw _)
  refine ⟨e,fun i=>?_,fun i live=>?_,fun i x U=>?_,?_⟩
  · by_cases h : o v∈Push.Local.patch P.activities i
    · simp only [e,if_pos h];exact mul_nonneg ht.le (Poly.nonnegative hw _)
    simp [e,h]
  · by_contra h;exact live (if_neg h)
  · by_cases h : o v∈Push.Local.patch P.activities i
    · have due := (Poly.member hw s (H.hard x i U)).trans ((covers i x U).reprice w hw)
      have gross := mul_le_mul_of_nonneg_left due ht.le
      simpa [e,h,t,←mul_assoc,ne_of_gt (Poly.worth hw s)] using gross
    · have vanish : (H.hard x i U).part s=0 := by
        by_contra live;exact h ((H.locality x i).carry U s live v member)
      simp [e,h,vanish]
  have paid:=sumBudget_mul_left (spent (o v)) ht.le
  convert paid using 1
  ext i
  by_cases h : o v∈Push.Local.patch P.activities i
  · change Real.exp _*(if o v∈Push.Local.patch P.activities i then _ else _)=t*(if o v∈Push.Local.patch P.activities i then _ else _)
    rw [if_pos h,if_pos h];ring
  change Real.exp _*(if o v∈Push.Local.patch P.activities i then _ else _)=t*(if o v∈Push.Local.patch P.activities i then _ else _)
  simp [h]

def unit (i : ℕ) : Finset ℕ := {i}
def pair (z : ℕ×ℕ) : Finset ℕ := {z.1,z.2}
def joined (e k : ℕ→ℝ) (z : ℕ×ℕ) := if z.1=z.2 then 0 else e z.1*k z.2

theorem single (s : R.Mode) (v : V) (member : v∈s.val) {κ : ℝ}
    (wallet : H.Paid w P.p.B P.p.supportExponent κ) (Z : Support n) (root : o v∈Z) :
    ∃ e : ℕ→ℝ,(∀ i,0≤e i) ∧ (∀ i,e i≠0→∀ j∈unit i,∃ u∈Z,u∈Push.Local.patch P.activities j) ∧
      (∀ i x U,‖(H.hard x i U).part s‖≤e i) ∧ SumBudget (fun i=>reservedMass P.p Z (salary P unit e i))
        (Real.exp ((P.p.supportExponent+2)*coverNumber P.p.B Z)*((Poly.toll w s)⁻¹*κ)) := by
  obtain ⟨e,he,loc,cap,paid⟩:=original H w hw s v member wallet
  refine ⟨e,he,fun i live j hj=>?_,cap,?_⟩
  · have eq : j=i := mem_singleton.mp hj
    exact ⟨o v,root,eq.symm ▸ loc i live⟩
  simpa only [salary,unit,sum_singleton,reservedMass] using
    sumBudget_mul_left paid (Real.exp_pos ((P.p.supportExponent+2)*coverNumber P.p.B Z)).le

theorem couple (a b : V) {κ : ℝ} (wallet : H.Paid w P.p.B P.p.supportExponent κ)
    (Z : Support n) (za : o a∈Z) (zb : o b∈Z) :
    ∃ e k : ℕ→ℝ,(∀ i,0≤e i) ∧ (∀ i,0≤k i) ∧
      (∀ z,joined e k z≠0→∀ j∈pair z,∃ u∈Z,u∈Push.Local.patch P.activities j) ∧
      (∀ i x U,‖(H.hard x i U).part (R.fire a)‖≤e i) ∧
      (∀ i x U,‖(H.hard x i U).part (R.fire b)‖≤k i) ∧
      SumBudget (fun z=>reservedMass P.p Z (salary P pair (joined e k) z))
        (Real.exp ((P.p.supportExponent+2)*coverNumber P.p.B Z)*(((w a)⁻¹*κ)*((w b)⁻¹*κ))) := by
  obtain ⟨e,ep,ea,eCap,eFee⟩:=original H w hw (R.fire a) a (mem_singleton_self _) wallet
  obtain ⟨k,kp,kb,kCap,kFee⟩:=original H w hw (R.fire b) b (mem_singleton_self _) wallet
  refine ⟨e,k,ep,kp,fun z live j hj=>?_,eCap,kCap,?_⟩
  · have diff : z.1≠z.2 := by intro eq;exact live (if_pos eq)
    rw [joined,if_neg diff] at live
    rcases mem_insert.mp hj with h|j2
    · subst j;exact ⟨o a,za,ea _ (left_ne_zero_of_mul live)⟩
    · obtain rfl : j=z.2 := mem_singleton.mp j2
      exact ⟨o b,zb,kb _ (right_ne_zero_of_mul live)⟩
  have paid:=sumBudget_mul_left (budget_prod eFee kFee) (Real.exp_pos ((P.p.supportExponent+2)*coverNumber P.p.B Z)).le
  simp only [Poly.solo_toll] at paid
  apply sumBudget_mono paid (fun z=>?_) (fun z=>?_) le_rfl
  · unfold reservedMass salary
    apply mul_nonneg (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le _)
    by_cases same : z.1=z.2
    · simp [joined,same]
    simpa [joined,same] using mul_nonneg (ep z.1) (kp z.2)
  by_cases same : z.1=z.2
  · simp only [reservedMass,salary,joined,if_pos same,mul_zero]
    exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (mul_nonneg (Real.exp_pos _).le (ep _)) (mul_nonneg (Real.exp_pos _).le (kp _)))
  have diff : z.1∉({z.2}:Finset ℕ) := by simpa using same
  simp only [reservedMass,salary,pair,sum_insert diff,sum_singleton,joined,if_neg same,mul_add,Real.exp_add]
  exact le_of_eq (by ring)

end YM.Integration.WilsonCenteredHardWallet
