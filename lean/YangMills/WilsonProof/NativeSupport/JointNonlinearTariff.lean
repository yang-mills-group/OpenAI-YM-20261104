import YangMills.WilsonProof.NativeSupport.InflatedTransfer
import YangMills.WilsonProof.NativeSupport.JointExpansion

/-! Restore the actual single-state measured tariff at each original root.
One family of coefficient majorants works for all roots simultaneously.
Support exponents are retained exactly. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.JointShadow
open Finset Lattice RG Wilson Marker Extra.Trajectories Painted MergeProof MergeProof.Accent
open scoped Classical BigOperators
variable {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] {G : Gauge} {n : Side}
local notation "B" => Stock.census (Ink V)
local notation "M" => (Stock.census (Ink V)).Mode

theorem rooted_nonlinear {b : ℕ} {e C t A D : ℝ} (a : 1≤A) (d : 1≤D)
    (w : V→ℝ) (hw : ∀ v,0<w v) (fresh : Finset V) {X : I → Support n}
    (o : V → Site n) (F : I → Config G n → Poly B)
    (borne : ∀ i,Borne (o ∘ Prod.fst) (X i) (F i) t)
    (h : Towed (weight w A D fresh) X F b e C) :
    ∃ v : I → M → ℝ, (∀ i S,0 ≤ v i S) ∧ (∀ i U S,‖(F i U).part S‖≤v i S) ∧
      ∀ y : V, min D (A^2) * (∑ i : I,
        (∑ S : M with y∈S.val.image Prod.fst ∧ gains fresh S.val,
          Poly.toll (fun p : Ink V=>w p.1) S*v i S) *
        Real.exp (e*coverNumber b (X i))) ≤ C := by
  obtain ⟨u,_,hit,per⟩:= h
  choose major pos bounded bill using per
  let v (i:I) (S:M) := if Menu.Vivid F i S then major i S else 0
  have nv (i:I) (S:M) : 0 ≤ v i S := by unfold v; split; exact pos i S; rfl
  have dom (i:I) (S:M) : v i S ≤ major i S := by unfold v; split; rfl; exact pos i S
  have obs (i:I) (U : Config G n) (S:M) : ‖(F i U).part S‖ ≤ v i S := by
    by_cases seen : Menu.Vivid F i S
    · exact (bounded i U S).trans_eq (if_pos seen).symm
    · have z : (F i U).part S=0 := not_not.mp fun h=>seen ⟨U,h⟩
      rw [z,norm_zero]
      exact nv i S
  refine ⟨v,nv,obs,fun y=>?_⟩
  let Q (i:I) := Finset.univ.filter fun S : M=>y∈S.val.image Prod.fst ∧ gains fresh S.val
  let base (S:M):=Poly.toll (fun p : Ink V=>w p.1) S
  let loaded (S:M):=Poly.toll (weight w A D fresh) S
  let L₀ := min D (A^2)
  have wp (p : Ink V) : 0<weight w A D fresh p := by
    have p0:=hw p.1
    have a0 : 0<A := zero_lt_one.trans_le a
    have d0 : 0<D := zero_lt_one.trans_le d
    unfold Painted.weight; split <;> split <;> positivity
  have at_root (i:I) (S:M) (hs:S∈Q i) (hv:v i S≠0) : o y∈X i := by
    have seen : Menu.Vivid F i S := by by_contra hn; exact hv (if_neg hn)
    obtain ⟨U,nonzero⟩:=seen
    obtain ⟨p,hp,rfl⟩:=mem_image.mp (mem_filter.mp hs).2.1
    exact (borne i).place S U nonzero (mem_image_of_mem _ hp)
  have local_cost (i:I) : L₀*(∑ S∈Q i,base S*v i S) ≤ u i := by
    calc _ ≤ ∑ S∈Q i,loaded S*major i S := by
              rw [mul_sum]
              apply sum_le_sum
              intro S hs
              rw [←mul_assoc]
              exact (mul_le_mul_of_nonneg_right (earned a d w hw fresh S (mem_filter.mp hs).2.2) (nv i S)).trans
                (mul_le_mul_of_nonneg_left (dom i S) (Poly.worth wp _).le)
         _ ≤ ∑ S:M,loaded S*major i S := sum_le_sum_of_subset_of_nonneg (subset_univ _)
               (fun S _ _=>mul_nonneg (Poly.worth wp S).le (pos i S))
         _ ≤ _ := bill i
  have paid := Extra.Multi.Budget.cap (hit (o y)) univ
  change L₀ * (∑ i : I,(∑ S∈Q i,base S*v i S)*Real.exp (e*coverNumber b (X i))) ≤ C
  refine le_trans ?_ paid
  rw [mul_sum]
  apply sum_le_sum
  intro i _
  by_cases contains : o y∈X i
  · rw [if_pos contains,←mul_assoc]
    exact mul_le_mul_of_nonneg_right (local_cost i) (Real.exp_pos _).le
  · have vanish : (∑ S∈Q i,base S*v i S)=0 := by
      apply sum_eq_zero
      intro S hs
      rw [show v i S=0 from not_not.mp (fun hn=> contains (at_root i S hs hn)),mul_zero]
    rw [if_neg contains,vanish,zero_mul,mul_zero]

end YM.Integration.InletSusceptibility.JointShadow
