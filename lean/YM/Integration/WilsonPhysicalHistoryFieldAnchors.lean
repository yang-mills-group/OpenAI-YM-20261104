import YM.Integration.WilsonPhysicalHistoryFieldBank
import YM.MSbar.Bout.Vaults

/-! Exact price of putting several already translated true torus inputs
at a common physical anchor before their joint normalized block integral. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonPhysicalHistoryFieldAnchors
open Function Finset Lattice RG Precision Wilson MSbar MSbar.Whisk MSbar.Cacao Push.Uniform
open FVA1Physical.Round2.Curvature
open scoped Classical BigOperators
variable {σ : Type} [Fintype σ] {n : Side}

omit [Fintype σ] in
private theorem moveWord (l : σ → Site n) (x y : Site n) {a : ℝ} (a0 : 0≤a) (s : ℕ)
    (v : List σ) :
    Whisk.spread l {y} a s v ≤ Whisk.liftW a s (separation y x) * Whisk.spread l {x} a s v := by
  classical
  let Z := Whisk.zone l {x} v
  have incl : Whisk.zone l {y} v ⊆ {y}∪Z := by
    intro q h
    rcases Finset.mem_union.mp h with r|r
    · exact Finset.mem_union_left _ r
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ r)
  have hx : x∈Z := Finset.mem_union_left _ (Finset.mem_singleton_self x)
  have u := Whisk.w_cast incl (Finset.mem_singleton_self y) hx a0 s
  simpa only [Whisk.spread,Z,Whisk.extent,Finset.sup_singleton,separation_self,
    Whisk.liftW,Nat.cast_zero,add_zero,mul_zero,Real.exp_zero,mul_one,one_pow,one_mul] using u

/-- The explicit offset cost, valid for any actual displaced positions. -/
theorem move (l : σ → Site n) (x y : Site n) {a t : ℝ} (a0 : 0≤a) (s m : ℕ)
    (P : Pot σ) (h : Whisk.Vault l {x} a s m 0 P t) :
    Whisk.Vault l {y} a s m 0 P (Whisk.liftW a s (separation y x)*t) := by
  classical
  let w := Whisk.liftW a s (separation y x)
  have w0 : 0≤w := (Whisk.wpos ..).le
  refine ⟨mul_nonneg w0 h.1,?_⟩
  intro r hr
  unfold Whisk.lump
  rw [word_function_sum]
  calc
    _ ≤ ∑ v : Fin r → σ, w * Whisk.rate l {x} a s 0 P (List.ofFn v) := by
      apply Finset.sum_le_sum
      intro v _
      unfold Whisk.rate
      exact (mul_le_mul_of_nonneg_right (moveWord l x y a0 s (List.ofFn v))
        (abs_nonneg _)).trans_eq (mul_assoc ..)
    _ = w*Whisk.lump l {x} a s r 0 P := by
      rw [←Finset.mul_sum,Whisk.lump,word_function_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (h.2 r hr) w0

end YM.Integration.WilsonPhysicalHistoryFieldAnchors

