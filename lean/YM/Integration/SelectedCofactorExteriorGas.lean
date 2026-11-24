import YM.Integration.ActualWilsonJoinedCofactor
import YM.Integration.NativeCoveredCofactorLocalUpdate
import YM.Planned.ATOM_FORCED_ESTIMATE.Outside

/-! The native unmarked exterior gas is shared by every interior inventory
on the same physical puncture and reads only the original inspected exterior. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SelectedCofactorExteriorGas
open Finset Lattice Wilson RG Planned.Forced Push.Local
open ActualWilsonPacketSplit ActualWilsonJoinedCofactor NativeCoveredCofactorLocalUpdate
open scoped Classical BigOperators
variable {G : Gauge} {n : Side}

private theorem parts {α : Type*} [DecidableEq α] (Y Z D F : Finset α)
    (hZ : Z ⊆ Y) (hd : Disjoint Y D) :
    Z ∪ D = F ↔ Y ∩ F = Z ∧ D = F \ Y := by
  constructor
  · rintro rfl
    constructor <;> ext x <;> simp only [mem_inter,mem_union,mem_sdiff]
    all_goals
      have ha : x ∈ Z → x ∈ Y := fun hz => hZ hz
      have hb : x ∈ Y → x ∉ D := fun hx hy => disjoint_left.mp hd hx hy
      tauto
  · rintro ⟨hz,hf⟩
    rw [← hz,hf]
    ext x
    simp only [mem_union,mem_inter,mem_sdiff]
    tauto

theorem permits_iff (P : Rep G n) (Y Z : Support n) (hZ : Z ⊆ Y)
    (J : Finset ℕ) (U : Config G n) :
    permits P Y Z J U ↔ Y ∩ flags P.p.threshold U = Z ∧ ExteriorOK P.activities P.p Y U J := by
  let D := J.biUnion (inventory P)
  have hd (hc : ∀ j ∈ J, Disjoint Y (scopes P j)) : Disjoint Y D := by
    apply disjoint_left.mpr
    intro y hy hm
    obtain ⟨j,hj,hi⟩ := mem_biUnion.mp hm
    exact disjoint_left.mp (hc j hj) hy ((P.activities.forced j).inventory_sup hi)
  constructor
  · rintro ⟨hp,hc,hf⟩
    obtain ⟨hz,hf'⟩ := (parts Y Z D _ hZ (hd hc)).mp hf
    exact ⟨hz,hp,hc,hf'⟩
  · rintro ⟨hz,hp,hc,hf⟩
    exact ⟨hp,hc,(parts Y Z D _ hZ (hd hc)).mpr ⟨hz,hf⟩⟩

theorem waiting_eq (P : Rep G n) (Y Z : Support n) (hZ : Z ⊆ Y)
    (J : Finset ℕ) (U : Config G n) :
    waiting P Y Z J U = if Y ∩ flags P.p.threshold U = Z then
      (outsideTerm P.activities P.p Y U J : ℂ) else 0 := by
  rw [waiting,permits_iff P Y Z hZ J U]
  by_cases hi : Y ∩ flags P.p.threshold U = Z <;>
    by_cases ho : ExteriorOK P.activities P.p Y U J <;>
    simp [hi,ho,outsideTerm]

theorem gas (P : Rep G n) (Y Z : Support n) (hZ : Z ⊆ Y) (U : Config G n) :
    (∑' J, waiting P Y Z J U) = if Y ∩ flags P.p.threshold U = Z then
      (outsideGas P.activities P.p Y U : ℂ) else 0 := by
  simp_rw [waiting_eq P Y Z hZ]
  by_cases hi : Y ∩ flags P.p.threshold U = Z
  · rw [if_pos hi]
    simp only [if_pos hi]
    exact (Complex.ofReal_tsum _).symm
  · simp only [if_neg hi,tsum_zero]

/-- On a filled puncture the genuine exterior gas is exactly the empty
spectator product for every original vacuum activity. -/
theorem filled (P : Rep G n) (Y : Support n) (U : Config G n)
    (hF : flags P.p.threshold U ⊆ Y) : outsideGas P.activities P.p Y U = 1 := by
  have hf : flags P.p.threshold U \ Y = ∅ := sdiff_eq_empty_iff_subset.mpr hF
  have hz (J : Finset ℕ) (hJ : J ≠ ∅) : outsideTerm P.activities P.p Y U J = 0 := by
    apply if_neg
    intro h
    obtain ⟨j,hj⟩ := nonempty_iff_ne_empty.mpr hJ
    obtain ⟨y,hy⟩ := (P.activities.forced j).inventory_ne
    have hh : y ∈ J.biUnion (flagsFor P.activities) := mem_biUnion.mpr ⟨j,hj,hy⟩
    rw [h.2.2,hf] at hh
    exact notMem_empty _ hh
  unfold outsideGas
  rw [tsum_eq_single ∅ hz]
  simp [outsideTerm,ExteriorOK,hf,Separate]

private theorem restrict_flags (Y S F F' : Support n) (hd : Disjoint Y S)
    (he : F \ Y = F' \ Y) : S ∩ F = S ∩ F' := by
  ext y
  by_cases hs : y ∈ S
  · have hy : y ∉ Y := fun h => disjoint_left.mp hd h hs
    have eqv : y ∈ F \ Y ↔ y ∈ F' \ Y := by rw [he]
    simpa only [mem_inter,hs,true_and,mem_sdiff,hy,not_false_eq_true,and_true] using eqv
  · simp only [mem_inter,hs,false_and]

/-- Changes of the fields and flags inside the puncture leave every
unchanged spectator at its actual gauge-field argument outside the puncture. -/
theorem exterior_eq (P : Rep G n) (hK : P.activities.ForcedFamily P.p) (Y : Support n)
    (U W : Config G n) (hU : Agrees (↑(univ \ Y : Support n) : Set (Site n)) U W)
    (hF : flags P.p.threshold U \ Y = flags P.p.threshold W \ Y) :
    outsideGas P.activities P.p Y U = outsideGas P.activities P.p Y W := by
  apply tsum_congr
  intro J
  have he : ExteriorOK P.activities P.p Y U J ↔ ExteriorOK P.activities P.p Y W J := by
    unfold ExteriorOK
    rw [hF]
  by_cases ho : ExteriorOK P.activities P.p Y U J
  · rw [outsideTerm,outsideTerm,if_pos ho,if_pos (he.mp ho)]
    apply prod_congr rfl
    intro j hj
    have hc := ho.2.1 j hj
    have hs : scopes P j ⊆ (univ \ Y : Support n) := fun z hz =>
      mem_sdiff.mpr ⟨mem_univ _,fun hy => disjoint_left.mp hc hy hz⟩
    exact hK.reads j U W (agrees_mono hU hs) (restrict_flags Y _ _ _ hc hF)
  · rw [outsideTerm,outsideTerm,if_neg ho,if_neg (fun h => ho (he.mpr h))]

theorem inspected_eq (P : Rep G n) (hK : P.activities.ForcedFamily P.p) (Y : Support n)
    (U W : Config G n) (hU : Agrees (inspected (univ \ Y)) U W) :
    outsideGas P.activities P.p Y U = outsideGas P.activities P.p Y W := by
  let X : Support n := univ \ Y
  have hA : Agrees X U W := agrees_mono hU (fun y hy => mem_union_left _ hy)
  have hf := flags_agree P.p.threshold U W X hU
  have he (F : Support n) : X ∩ F = F \ Y := by
    ext y
    simp only [X,mem_inter,mem_sdiff,mem_univ,true_and,and_comm]
  rw [he,he] at hf
  exact exterior_eq P hK Y U W hA hf

end YM.Integration.SelectedCofactorExteriorGas
end
