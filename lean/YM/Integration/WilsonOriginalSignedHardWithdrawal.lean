import YM.Integration.WilsonOriginalSeparatedHardSuccessor

/-! The changed signed hard owner is selected inside each complete original admissible cover. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalSignedHardWithdrawal
open Function Finset Marker QuadraticLocal RG Lattice Wilson
open WilsonForcedMarkerLine
open scoped BigOperators Classical

variable {V ι : Type*} [DecidableEq V] [DecidableEq ι] {R:Marker.Census V} {v:V}

/-- Every other factor in this coefficient is the original held hard factor. -/
theorem selection (S:Finset ι) (A K:ι→Poly R) (support:∀ i∈S,pinned v (K i-A i)) :
    pinned v ((∏ i∈S,K i)-(∏ i∈S,A i)) ∧
    (∏ i∈S,K i)-(∏ i∈S,A i)=∑ i∈S,(K i-A i)*(∏ j∈S.erase i,K j) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [pinned]
  | @insert x S missing ih =>
    have old:=ih (fun i hi=>support i (Finset.mem_insert_of_mem hi))
    have single:=support x (Finset.mem_insert_self x S)
    have both:=square single old.1
    have diff:(∏ i∈insert x S,K i)-(∏ i∈insert x S,A i)=
          (K x-A x)*(∏ i∈S,K i)+K x*((∏ i∈S,K i)-(∏ i∈S,A i)) := by
      rw [prod_insert missing,prod_insert missing]
      linear_combination -both
    rw [diff]
    constructor
    · apply pin_sum (pin_left single _)
      rw [mul_comm]
      exact pin_left old.1 _
    · rw [old.2,mul_sum,sum_insert missing,erase_insert missing]
      congr 1
      apply sum_congr rfl
      intro i hi
      have ne:i≠x:=fun same=>missing (same ▸ hi)
      rw [erase_insert_of_ne ne.symm,prod_insert]
      · ring
      · exact fun present=>missing (mem_of_mem_erase present)

open QuadraticLocal.Fusion.Attached
variable {G : Gauge} {n:Side} {P:Rep G n} {o:V→Site n} {T I:Type*}
  (A K:Hard T P.p P.activities.forced P.activities.K o R)

def selected (t:T) (U:Config G n) (S:Finset ℕ) : Poly R :=
  if P.activities.admissible P.p U S then
    ∑ i∈S,(K.hard t i U-A.hard t i U)*(∏ j∈S.erase i,K.hard t j U)
  else 0

theorem admitted (t:T) (U:Config G n) (S:Finset ℕ)
    (marked:∀ i,pinned v (K.hard t i U-A.hard t i U)) :
    packet P.activities P.p (K.hard t) U S-packet P.activities P.p (A.hard t) U S=
    selected A K t U S := by
  by_cases allowed:P.activities.admissible P.p U S
  · simpa only [packet,selected,if_pos allowed] using
      (selection S (fun i=>A.hard t i U) (fun i=>K.hard t i U) (fun i _=>marked i)).2
  · simp [packet,selected,allowed]

theorem held [Fintype V] (E:Lamps T I G P.p o R) {w:V→ℝ} {a b:ℝ}
    (base:A.Paid w P.p.B P.p.supportExponent a)
    (actual:K.Paid w P.p.B P.p.supportExponent b) (hw:∀i,0<w i) (t:T) (U:Config G n)
    (marked:∀ i,pinned v (K.hard t i U-A.hard t i U)) :
    let kept : Gallery T I o P R := ⟨E,K⟩
    let gone : Gallery T I o P R := ⟨E,A⟩
    kept.density t U-gone.density t U=
      (Complex.ofReal (Real.exp (P.exponent U))) •
        (Poly.pass (E.log t U)*∑' S:Finset ℕ,selected A K t U S) := by
  have h₀:=Hard.packet_summing A base P.p.exponent_pos.le hw t U
  have h₁:=Hard.packet_summing K actual P.p.exponent_pos.le hw t U
  have gas : (∑' S:Finset ℕ,packet P.activities P.p (K.hard t) U S)-
      (∑' S:Finset ℕ,packet P.activities P.p (A.hard t) U S)=
      ∑' S:Finset ℕ,selected A K t U S := by
    rw [←h₁.tsum_sub h₀]
    exact tsum_congr (fun S=>admitted A K t U S marked)
  dsimp [Gallery.density,Gallery.gas]
  rw [←smul_sub,←mul_sub,gas]

end YM.Integration.WilsonOriginalSignedHardWithdrawal
