import YangMills.WilsonProof.NativeSupport.ScalarCompensation
import YM.MergeProof.Sigil

/-! Grade the *original* forced reclosure by the number of fresh dirty
measurements. The constant coefficient is the complete old marked gas. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.InletSusceptibility
open Finset Lattice RG Wilson Marker MergeProof MergeProof.Accent
open scoped BigOperators Classical
variable {V J : Type*} [DecidableEq V] [Fintype J] {G : Gauge} {n : Side} {B : Census V}
variable (K : Box n → Config G n → Poly B) (u : J → Config G n → Poly B)
variable (X : J → Support n) (t : ℝ) (U : Config G n) (p : Box n)

omit [Fintype J] in
theorem fresh_degree (z : ℂ) (θ : Finset J) :
    briar K (fun i F => z • u i F) X t U p θ = z^θ.card • briar K u X t U p θ := by
  unfold briar
  rw [Finset.smul_sum]
  apply sum_congr rfl
  intro D _
  unfold tallyHead
  split
  · simp only [prod_disjSum,pork,Sum.elim_inl,Sum.elim_inr,Finset.prod_smul,
      prod_const,mul_smul_comm]
  · rw [smul_zero]

theorem closure_grading (hK : ∀ i, K i U ≠ 0 → i.1 ∩ flags t U = i.2 ∧ Sure i) (z : ℂ) :
    closure K (fun i F => z • u i F) X t p U =
      K p U + ∑ θ : Finset J with θ.Nonempty, z^θ.card • briar K u X t U p θ := by
  rw [roster]
  simp_rw [fresh_degree]
  rw [← Finset.sum_filter_add_sum_filter_not (s:=univ) (p:=fun θ : Finset J => θ=∅)]
  simp only [sum_filter,ne_eq,Finset.nonempty_iff_ne_empty]
  have first : (∑ θ : Finset J, if θ=∅ then z^θ.card • briar K u X t U p θ else 0) = K p U := by
    simpa only [sum_ite_eq',mem_univ,if_true,card_empty,pow_zero,one_smul] using
      (show (∑ θ : Finset J, if θ=∅ then z^θ.card • briar K u X t U p θ else 0) = K p U from by
        simp [baseR K u X t U p hK])
  rw [first]

theorem closure_no_fresh (hK : ∀ i, K i U ≠ 0 → i.1 ∩ flags t U = i.2 ∧ Sure i) :
    closure K (fun _ : J => fun _ => 0) X t p U = K p U := by
  have h := closure_grading K (fun _ : J => fun _ => 0) X t U p hK (0:ℂ)
  simp only [zero_smul] at h
  rw [h,add_eq_left]
  apply sum_eq_zero
  intro θ hθ
  have hn : θ.Nonempty := (mem_filter.mp hθ).2
  rw [zero_pow (card_pos.mpr hn).ne',zero_smul]

end YM.Integration.InletSusceptibility
