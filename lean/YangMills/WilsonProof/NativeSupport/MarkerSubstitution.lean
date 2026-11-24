import YangMills.WilsonProof.NativeSupport.PacketPrice

/-! Substitution in the actual full marker census. Images may overlap, and
their support may contain a shared derivative marker. The only generator
relation needed for the substitution is its square-zero relation. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.MarkerSubstitution
open Finset Marker Extra.Trajectories Packet
open scoped BigOperators Classical
variable {I V : Type*} [Fintype I] [DecidableEq I] [DecidableEq V] {B : Census V}
local notation "Π₀" => Poly (Stock.census I)

def applyTo (r : I → Poly B) (P : Π₀) : Poly B :=
  ∑ S : Finset I, P.part (tag S) • ∏ i∈S, r i

theorem on_send (r : I → Poly B) (T : Finset I) (c : ℂ) :
    applyTo r (Poly.send (tag T) c)= c • ∏ i∈T, r i := by
  rw [applyTo,sum_eq_single T]
  · rw [Poly.part_send,if_pos rfl]
  · intro S _ hs
    rw [Poly.part_send,if_neg (fun e => hs (congrArg Subtype.val e)),zero_smul]
  · simp

private lemma on_sum {J : Type*} (r : I→Poly B) (F : Finset J) (u : J→Π₀) :
    applyTo r (∑ i∈F,u i) = ∑ i∈F,applyTo r (u i) := by
  simp only [applyTo,Poly.part_sum,sum_smul]
  rw [sum_comm]

theorem on_smul (r : I → Poly B) (c : ℂ) (P : Π₀) :
    applyTo r (c • P) = c • applyTo r P := by
  simp only [applyTo,Poly.part_smul,smul_smul,Finset.smul_sum]

private lemma parts (P : Π₀) : (∑ S : Finset I, Poly.send (tag S) (P.part (tag S)))=P := by
  ext S
  rw [Poly.part_sum,sum_eq_single S.val]
  · rw [Poly.part_send,if_pos (show S=tag S.val from rfl)]
  · intro T _ h
    rw [Poly.part_send,if_neg (fun e => h (congrArg Subtype.val e).symm)]
  · simp

private lemma monomials (r : I → Poly B) (null : ∀ i, r i*r i=0)
    (S T : Finset I) (a c : ℂ) :
    applyTo r (Poly.send (tag S) a * Poly.send (tag T) c) =
      applyTo r (Poly.send (tag S) a)*applyTo r (Poly.send (tag T) c) := by
  rw [on_send,on_send,smul_mul_smul_comm]
  by_cases h : Disjoint S T
  · rw [tagged_mul _ _ (tag (S∪T)) ⟨h,rfl⟩,on_send,prod_union h]
  · have z : Poly.send (tag S) a * Poly.send (tag T) c=0 := by
      by_contra hn
      obtain ⟨_,hd,_⟩ := merges_of_tagged_mul hn
      exact h hd
    rw [z,show applyTo r 0=0 by simp [applyTo,Poly.part_nil]]
    obtain ⟨i,hi,ht⟩ := not_disjoint_iff.mp h
    rw [← prod_erase_mul S r hi,← prod_erase_mul T r ht]
    rw [show ((∏ p ∈ S.erase i,r p)*r i)*((∏ p ∈ T.erase i,r p)*r i) =
      ((∏ p ∈ S.erase i,r p)*(∏ p ∈ T.erase i,r p))*(r i*r i) by ring,
      null,mul_zero,smul_zero]

theorem on_mul (r : I → Poly B) (null : ∀ i, r i*r i=0) (P Q : Π₀) :
    applyTo r (P*Q) = applyTo r P*applyTo r Q := by
  conv_lhs => rw [← parts P,← parts Q,sum_mul]
  simp_rw [mul_sum,on_sum,monomials r null]
  conv_rhs => rw [← parts P,← parts Q,on_sum,on_sum,sum_mul]
  simp_rw [mul_sum]

def hom (r : I → Poly B) (null : ∀ i, r i*r i=0) : Π₀ →+* Poly B where
  toFun := applyTo r
  map_zero' := by simp [applyTo,Poly.part_nil]
  map_one' := by
    unfold applyTo
    rw [sum_eq_single ∅]
    · rw [Poly.one_part,if_pos (show tag (∅:Finset I)=(Stock.census I).quiet from rfl)]
      simp
    · intro T _ h; rw [Poly.one_part,if_neg (fun e => h (congrArg Subtype.val e)),zero_smul]
    · simp
  map_add' _ _ := by simp only [applyTo,Poly.part_plus,add_smul,sum_add_distrib]
  map_mul' := on_mul r null

theorem on_pass [Fintype V] (r : I → Poly B) (null : ∀ i, r i*r i=0) (P : Π₀)
    (noScalar : P.part (Stock.census I).quiet=0) (proper : (applyTo r P).part B.quiet=0) :
    applyTo r (Poly.pass P) = Poly.pass (applyTo r P) := by
  let f := hom r null
  have power (n : ℕ) : applyTo r (P^n) = (applyTo r P)^n := map_pow f P n
  have hp (n : ℕ) (hn : Fintype.card I<n) : (applyTo r P)^n=0 := by
    rw [← power,Poly.stops P noScalar n hn]
    exact map_zero f
  let n := max (Fintype.card I) (Fintype.card V) + 1
  let C (k : ℕ) := (k.factorial:ℂ)⁻¹ • (applyTo r P)^k
  have widen (m : ℕ) (hm : m+1≤n) (hz : ∀ k, m<k → (applyTo r P)^k=0) :
      (∑ k∈range (m+1),C k) = ∑ k∈range n,C k := by
    apply sum_subset (fun k hk => mem_range.mpr (lt_of_lt_of_le (mem_range.mp hk) hm))
    intro k _ h
    have hk : m<k := by simpa only [mem_range,not_lt,Nat.succ_le_iff] using h
    simp only [C,hz _ hk,smul_zero]
  simp only [Poly.pass,on_sum,on_smul,power]
  exact (widen _ (Nat.add_le_add_right (le_max_left ..) 1) hp).trans
    (widen _ (Nat.add_le_add_right (le_max_right ..) 1) (Poly.stops _ proper)).symm

end YM.Integration.InletSusceptibility.MarkerSubstitution
