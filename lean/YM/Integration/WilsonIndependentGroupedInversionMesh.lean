import YM.XSpace.Regulated

/-! Group a prescribed odd-ratio XSpace regulator at its exact top sites and even period. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentGroupedInversionMesh

open Lattice XSpace
open scoped Classical BigOperators
variable (V : XSpace.Run) (u i : ℕ)

def block := V.ratio^u
def younger := i%u
def later := V.reserve*i*i
def older := (later V i + younger u i)%u
def zoom := V.ratio ^ younger u i

theorem first (hu:0<u) : Odd (block V u) ∧ 3 ≤ block V u ∧ younger u i < u ∧ older V u i < u := by
  refine ⟨V.odd.pow,?_,Nat.mod_lt _ hu,Nat.mod_lt _ hu⟩
  exact V.large.trans (Nat.le_self_pow (by omega) _)

theorem floor (N:ℕ) : ∃ u:ℕ, 0<u ∧ N≤block V u := by
  have base : 1 < V.ratio := by have := V.large;omega
  exact ⟨N+1,Nat.succ_pos _, (Nat.le_succ N).trans ((Nat.lt_pow_self base).le)⟩

private theorem ratio_pos : 0<V.ratio := by have := V.large;omega
theorem zoom_pos : 0<zoom V u i := pow_pos (ratio_pos V) _

/-- The last residue changes the actual admissible even terminal side, before its block steps. -/
def terminal : Period :=
  ⟨⟨V.finalSide.side.val * V.ratio^(older V u i),Nat.mul_pos V.finalSide.side.pos (pow_pos (ratio_pos V) _)⟩,
    dvd_mul_of_dvd_left V.finalSide.even _,V.finalSide.large.trans (Nat.le_mul_of_pos_right _ (pow_pos (ratio_pos V) _))⟩

theorem top :
    (V.step i).p.side.val = (terminal V u i).side.val *
      block V u ^ (i/u+(later V i+younger u i)/u) := by
  have fine := Nat.mod_add_div i u
  have coarse := Nat.mod_add_div (later V i + i%u) u
  have gaps : i + later V i = older V u i + u*(i/u+(later V i + younger u i)/u) := by
    unfold older younger
    rw [Nat.mul_add]
    omega
  change V.finalSide.side.val*V.ratio^(i+later V i)=V.finalSide.side.val*V.ratio^(older V u i)*(V.ratio^u)^_
  rw [← pow_mul, mul_assoc, ← pow_add, gaps]

theorem residues (hu:0<u) :
    (terminal V u i).side.val ∈ Finset.univ.image (fun t:Fin u => V.finalSide.side.val*V.ratio^(t:ℕ)) :=
  Finset.mem_image.mpr ⟨⟨older V u i,(first V u i hu).2.2.2⟩,Finset.mem_univ _,rfl⟩

/-- Only the reporting unit changes. All native sites, pin aliases and the tree type are definitionally identical. -/
def mesh : Mesh :=
  ⟨(V.step i).p, (zoom V u i:ℝ)*(V.step i).spacing,mul_pos (by exact_mod_cast zoom_pos V u i) (V.step i).positive⟩

theorem spacing : (mesh V u i).spacing=((block V u:ℝ)^(i/u))⁻¹ := by
  have z : (V.ratio:ℝ)≠0 := Nat.cast_ne_zero.mpr (ratio_pos V).ne'
  change ((V.ratio^(i%u):ℕ):ℝ)*(↑(V.ratio^i):ℝ)⁻¹=((↑(V.ratio^u):ℝ)^(i/u))⁻¹
  push_cast
  have fine : (V.ratio:ℝ)^i = (V.ratio:ℝ)^(i%u) * ((V.ratio:ℝ)^u)^(i/u) := by
    rw [←pow_mul, ←pow_add, Nat.mod_add_div]
  rw [fine]
  field_simp

theorem period : (mesh V u i).size = ((terminal V u i).side.val:ℝ) *
    (block V u:ℝ)^((later V i+younger u i)/u) := by
  have b : (block V u:ℝ)≠0 := Nat.cast_ne_zero.mpr (pow_pos (ratio_pos V) _).ne'
  change (mesh V u i).spacing*((V.step i).p.side.val:ℝ)=_
  rw [spacing,top,pow_add]
  push_cast
  field_simp

end YM.Integration.WilsonIndependentGroupedInversionMesh
