import YM.Integration.WilsonThermometerWeakFineStops

/-! Two true reflection cells remain distinct after wrapping at the actual period,
uniformly in the fine mesh and in the common translating field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakSeparatedStops
open Function Filter Set Lattice Cells Frontier6.Platform
open scoped Topology Classical BigOperators

theorem separated (S:Schedule) (m N p:ℕ) (r:Fin 2→ℕ) (x u:Fin 2 → Cover) (a:Cover)
    (placed:∀i,atStop S m (u i) (3*S.a (r i)) (S.gridPoint N (x i+a)))
    (far:∃l:Axis,S.a m ≤ |S.gridPoint N (x 0) l-S.gridPoint N (x 1) l|)
    (period:∀l:Axis,2*(|S.gridPoint N (x 0) l-S.gridPoint N (x 1) l|+S.a m) <
      ((S.side m p).val:ℝ)*S.a m):
    wrap (S.side m p) (u 0)≠wrap (S.side m p) (u 1):=by
  let n:=S.side m p
  have plus (i:Fin 2)(j:Axis):S.gridPoint N (x i+a) j=S.gridPoint N (x i) j+S.gridPoint N a j:=by
    change S.a N*((x i j+a j:ℤ):ℝ)=_;rw [Int.cast_add,mul_add];rfl
  have err (j:Axis):|(S.gridPoint m (u 0) j-S.gridPoint m (u 1) j)-
      (S.gridPoint N (x 0) j-S.gridPoint N (x 1) j)|<S.a m:=by
    have a₀:=abs_lt.mp (placed 0 j);have a₁:=abs_lt.mp (placed 1 j)
    rw [plus] at a₀ a₁
    exact abs_lt.mpr ⟨by linarith only [a₀.2,a₁.1,S.a_pos (r 0),S.a_pos (r 1)],
      by linarith only [a₀.1,a₁.2,S.a_pos (r 0),S.a_pos (r 1)]⟩
  have safe (j:Axis):-(n.val:ℤ)<2*(u 0-u 1) j ∧ 2*(u 0-u 1) j≤n.val:=by
    have bounds:=abs_lt.mp (err j)
    have sides:=abs_le.mp (le_refl |S.gridPoint N (x 0) j-S.gridPoint N (x 1) j|)
    have ran:=period j
    change -(S.a m)< S.a m*(u 0 j:ℝ)- S.a m*(u 1 j:ℝ)-_ ∧
      S.a m*(u 0 j:ℝ)- S.a m*(u 1 j:ℝ)-_ < S.a m at bounds
    have lo:(-(n.val:ℝ))*S.a m < (2*((u 0 j:ℝ)-(u 1 j:ℝ)))*S.a m:=by
      dsimp only [n];linarith only [bounds.1,sides.1,ran]
    have hi:(2*((u 0 j:ℝ)-(u 1 j:ℝ)))*S.a m < (n.val:ℝ)*S.a m:=by
      dsimp only [n];linarith only [bounds.2,sides.2,ran]
    have low:=lt_of_mul_lt_mul_right lo (S.a_pos m).le
    have high:=(lt_of_mul_lt_mul_right hi (S.a_pos m).le).le
    constructor
    · change -(n.val:ℤ)<2*(u 0 j-u 1 j);exact_mod_cast low
    · change 2*(u 0 j-u 1 j)≤n.val;exact_mod_cast high
  intro eq
  have hz:(wrap n (u 0-u 1))=wrap n 0:=by
    funext j
    have same:=congrFun eq j
    change ((u 0 j:ℤ):Per n)=((u 1 j:ℤ):Per n) at same
    change ((u 0 j-u 1 j:ℤ):Per n)=((0:ℤ):Per n)
    rw [Int.cast_sub,same,sub_self,Int.cast_zero]
  have zero:(u 0-u 1)=0:=wrap_injOn n safe (fun _=>⟨by simp,by simp⟩) hz
  obtain ⟨j,gap⟩:=far
  have off:=err j
  rw [sub_eq_zero.mp zero,sub_self,zero_sub,abs_neg] at off
  exact (not_lt_of_ge gap) off

end YM.Integration.WilsonThermometerWeakSeparatedStops
end
