import YM.Lattice.Support

/-!
# Local mirror test, one axis

This is a way of testing translation sums *on nonlinear compatible fields*.
We reflect a `[-k,k]` patch to a `4k` torus of **test arguments**. There
will be no comparison of physical theories at the two periods. The step at
an endpoint is important (there is no stationary step).
-/

set_option autoImplicit false

namespace YM.Comparison.Density.Mirrors
open Lattice Function

def quad (k : Side) : Side := ⟨4*k.val, Nat.mul_pos (by decide) k.property⟩

/-- Coordinate of the old field read at a given reflected site. -/
def wave (k : Side) (x : Per (quad k)) : ℤ :=
  let a := ZMod.valMinAbs x
  if a < -(k.val : ℤ) then -2*(k.val:ℤ)-a
  else if a > (k.val:ℤ) then 2*(k.val:ℤ)-a
  else a

private lemma range_slot (k : Side) (x : Per (quad k)) :
    -(2*(k.val:ℤ)) < ZMod.valMinAbs x ∧ ZMod.valMinAbs x ≤ 2*(k.val:ℤ) := by
  have h:= ZMod.valMinAbs_mem_Ioc x
  change -(↑(4*k.val):ℤ)<_ ∧ _≤(↑(4*k.val):ℤ) at h
  push_cast at h
  omega

lemma wave_range (k : Side) (x : Per (quad k)) : -(k.val:ℤ)≤wave k x ∧ wave k x ≤ k.val := by
  have hf:= range_slot k x
  dsimp only [wave]
  split_ifs <;> omega

private lemma cast_slot (k : Side) (z : ℤ) (hl : -(2*(k.val:ℤ)) < z) (hu : z ≤ 2*(k.val:ℤ)) :
    ZMod.valMinAbs (z : Per (quad k)) = z := by
  refine (ZMod.valMinAbs_spec _ _).2 ⟨rfl,?_⟩
  change -(↑(4*k.val):ℤ)<_ ∧ _≤(↑(4*k.val):ℤ)
  push_cast
  omega

private lemma cast_turn (k : Side) : ((4*(k.val:ℤ):ℤ) : Per (quad k)) = 0 := by
  rw [show 4*(k.val:ℤ) = (↑(quad k).val : ℤ) by simp [quad]]
  simp [Per]

lemma wave_core (k : Side) (z : ℤ) (hl : -(k.val:ℤ)≤z) (hu : z ≤ k.val) :
    wave k (z : Per (quad k)) = z := by
  have hk : 0 < k.val := k.property
  dsimp only [wave]; rw [cast_slot _ _ (by omega) (by omega)]
  split_ifs <;> omega

lemma slot_injective (k : Side) (z w : ℤ) (hz₁ : -(k.val:ℤ) ≤ z) (hz₂ : z ≤ k.val)
    (hw₁ : -(k.val:ℤ) ≤ w) (hw₂ : w ≤ k.val) (h : (z : Per (quad k)) = w) : z = w := by
  rw [← wave_core k z hz₁ hz₂,← wave_core k w hw₁ hw₂,h]

lemma wave_lower (k : Side) (z : ℤ) (hl : -(3*(k.val:ℤ)) ≤ z) (hu : z ≤ -(k.val:ℤ)) :
    wave k (z : Per (quad k)) = -(2*(k.val:ℤ))-z := by
  dsimp only [wave]
  by_cases h : -(2*(k.val:ℤ)) < z
  · rw [cast_slot _ _ h (by omega)]; split_ifs <;> omega
  let w : ℤ := z+4*(k.val:ℤ)
  rw [show (z : Per (quad k)) = ↑w by unfold w; rw [Int.cast_add, cast_turn, add_zero],
      cast_slot k w (by have hk : 0 < k.val := k.property; dsimp only [w]; omega) (by dsimp only [w]; omega)]
  dsimp only [w]
  split_ifs <;> omega

lemma wave_upper (k : Side) (z : ℤ) (hl : (k.val:ℤ) ≤ z) (hu : z ≤ 3*(k.val:ℤ)) :
    wave k (z : Per (quad k)) = 2*(k.val:ℤ)-z := by
  rw [show (z : Per (quad k)) = ↑(z-4*(k.val:ℤ):ℤ) by rw [Int.cast_sub, cast_turn, sub_zero],
      wave_lower k _ (by omega) (by omega)]
  omega

lemma wave_period (k : Side) (x : Per (quad k)) :
    x = ((wave k x:ℤ) : Per (quad k)) ∨ x = ((2*(k.val:ℤ)-wave k x:ℤ) : Per (quad k)) := by
  let z:=ZMod.valMinAbs x
  have he : (z : Per (quad k))=x := ZMod.coe_valMinAbs x
  obtain ⟨hl,hp⟩ : -(2*(k.val:ℤ)) < z ∧ z ≤ 2*(k.val:ℤ) := range_slot ..
  by_cases hv : -(k.val:ℤ) ≤ z
  · by_cases hb : z ≤ k.val
    · left
      rw [← he,wave_core k z hv hb]
    right
    rw [← he,wave_upper k z (by omega) (by omega),sub_sub_cancel]
  right
  rw [← he,wave_lower k z (by omega) (by omega),
    show 2*(k.val:ℤ) - (-(2*(k.val:ℤ))-z)=z+4*(k.val:ℤ) by omega,
    Int.cast_add, cast_turn, add_zero]

lemma wave_reflect (k : Side) (x : Per (quad k)) :
    wave k (((2*(k.val:ℤ):ℤ) : Per (quad k))-x) = wave k x := by
  let z:=wave k x
  obtain ⟨hl,hp⟩ : -(k.val:ℤ)≤z ∧ z≤k.val := wave_range ..
  change _ = z
  rcases wave_period k x with h|h
  · change x=(z : Per (quad k)) at h
    rw [h,← Int.cast_sub,wave_upper k _ (by omega) (by omega)]; omega
  change x=((2*(k.val:ℤ)-z : ℤ) : Per (quad k)) at h
  rw [h,← Int.cast_sub,sub_sub_cancel,wave_core k z hl hp]

lemma wave_neg (k : Side) (x : Per (quad k)) : wave k (-x) = -wave k x := by
  let z:=wave k x
  obtain ⟨hl,hp⟩ : -(k.val:ℤ)≤z ∧ z≤k.val := wave_range ..
  change _ = -z
  rcases wave_period k x with h|h
  · change x=(z : Per (quad k)) at h
    rw [h,← Int.cast_neg,wave_core k _ (by omega) (by omega)]
  change x=((2*(k.val:ℤ)-z:ℤ) : Per (quad k)) at h
  rw [h,← Int.cast_neg,wave_lower k _ (by omega) (by omega)]; omega

lemma wave_step (k : Side) (x : Per (quad k)) :
    wave k (x+1)=wave k x+1 ∨ wave k (x+1)=wave k x-1 := by
  let z:=wave k x
  have hk : 0 < (k.val:ℤ) := by exact_mod_cast (show 0 < k.val from k.property)
  obtain ⟨hl,hp⟩ : -(k.val:ℤ) ≤ z ∧ z ≤ k.val := wave_range ..
  change _ = z+1 ∨ _=z-1
  rcases wave_period k x with h|h
  · by_cases hh : z<k.val
    · left
      change x=(z : Per (quad k)) at h
      rw [h, ← Int.cast_one (R:=Per (quad k)), ← Int.cast_add]
      exact wave_core _ _ (by omega) (by omega)
    right
    change x=(z : Per (quad k)) at h
    rw [h, ← Int.cast_one (R:=Per (quad k)), ← Int.cast_add, wave_upper k (z+1) (by omega) (by omega)]; omega
  by_cases hh : -(k.val:ℤ) < z
  · right
    change x=((2*(k.val:ℤ)-z:ℤ) : Per (quad k)) at h
    rw [h, ← Int.cast_one (R:=Per (quad k)), ← Int.cast_add,wave_upper k _ (by omega) (by omega)]; omega
  left
  change x=((2*(k.val:ℤ)-z:ℤ) : Per (quad k)) at h
  have he : x=(z:Per (quad k)) := h.trans (by
    rw [show 2*(k.val:ℤ) - z=z+4*(k.val:ℤ) by omega, Int.cast_add,cast_turn,add_zero])
  rw [he, ← Int.cast_one (R:=Per (quad k)), ← Int.cast_add]
  exact wave_core _ _ (by omega) (by omega)

end YM.Comparison.Density.Mirrors
