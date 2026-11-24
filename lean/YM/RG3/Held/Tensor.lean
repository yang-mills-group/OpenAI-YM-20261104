import YM.RG3.Held.Lives

/-!
# Continuing receipts past unit test supplies

Only for true multilinear test assistance (upstream presentation may use
additional coupled test operators on whole lattice; to apply, use authorized
pure external products or bound them by the independently authorized input
kernel norm). Preserves test order. Ability to differentiate K values in U
or take analytic slopes in coupling NOT obtained.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Held
open Marker Finset Function Filter
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {V : Type*} [DecidableEq V] (T : V → Type*) [∀ i,NormedAddCommGroup (T i)]

-- Scale all named arguments to the unit envelope. Only the named positions
-- count. For summability purposes ONLY, with no uniform bound on #V or
-- norm equivalence. Quantitative consumers use bounds on `unit T x`.
def unit (z : Π v,T v) := ∀ i, ‖z i‖ ≤ 1

namespace Letter
variable {K : Type*} [RCLike K] [∀ i, NormedSpace K (T i)]
variable {T} {E : Type*} [NormedAddCommGroup E] [NormedSpace K E]

lemma cost {s : Finset V} {f : (Π v,T v) → E} (h : Letter K T s f) (z) {a : ℝ} (ha : ∀ z,unit T z → ‖f z‖ ≤ a) :
    ‖f z‖ ≤ (∏ i∈s,‖z i‖)*a := by
  -- scale coordinates explicitly, handling zero separately
  by_cases he : ∃ i∈s,z i = 0
  · obtain ⟨i,hi,hh⟩ := he
    have hval : (∏ i∈s,‖z i‖) = 0 := prod_eq_zero hi (by rw [hh,norm_zero])
    have ht : f z = 0 := by
      have hh' : z = update z i ((0:K) • z i) := by rw [zero_smul,← hh,update_eq_self]
      rw [hh',h.scale _ i hi,zero_smul] -- specify scalar type
    simp [ht,hval]
  -- unit normalized via RCLike.ofReal
  let c (i : V) : K := ((‖z i‖:ℝ) : K)
  let y (x : Finset V) (i : V) := if i∈x then (c i)⁻¹ • z i else z i
  have hc (i : V) : ‖c i‖=‖z i‖ := by simp [c]
  have hn {i} (hi:i∈s) : c i ≠ 0 := fun h => he ⟨i,hi,norm_eq_zero.mp (by rw [← hc,h,norm_zero])⟩
  suffices hd : ∀ p : Finset V,p⊆s → ‖f z‖=(∏ i∈p,‖z i‖) * ‖f (y p)‖ by
    let u (i:V) := if i∈s then y s i else 0
    have ht i (hh : i∈s) : ‖y s i‖ ≤ 1 := by rw [show y s i = _ from if_pos hh,norm_smul,norm_inv]; rw [← hc,_root_.inv_mul_cancel₀ (show ‖c i‖ ≠ 0 from by simp [hn hh])] -- replace ‖z i‖
    rw [hd s (Finset.Subset.refl _),h.stay (y s) u (fun i hi => (if_pos hi).symm)]
    exact mul_le_mul_of_nonneg_left (ha u (fun i => by unfold u; split <;> first | exact ht _ (by assumption) | simp)) (prod_nonneg fun i _ => norm_nonneg _)
  intro p hp
  induction p using Finset.induction_on with
  | empty => simp [y]
  | insert i p hi ih =>
    have he' : i∈s := hp (mem_insert_self ..)
    have hy : y (insert i p)=update (y p) i ((c i)⁻¹ • z i) := by
      funext j; by_cases hj : j=i
      · subst j; simp [y]
      simp [y,hj,update_of_ne]
    rw [ih (insert_subset_iff.mp hp).2, prod_insert hi,hy,h.scale _ i he']
    rw [show update (y p) i (z i)=y p from ?_, norm_smul, norm_inv, hc]
    · field_simp
      have hx : 0 < ‖z i‖ := norm_pos_iff.mpr (fun h' => he ⟨i,he',h'⟩)
      field_simp
    rw [show z i=y p i from Eq.symm (if_neg hi)] -- unknown dependent transports
    exact update_eq_self i _

end Letter
end YM.RG3.Held
