import YM.Integration.WilsonAddressedWeakCalibration

/-! Actual separation of the two weak detector roots on the reporting torus.
The two finite geometric hypotheses are in physical units. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedWeakSeparation
open Function Filter Set MeasureTheory Lattice Wilson RG Extra.Histories RG05Readout Native
open Extraction XSpace Push.GridApprox Table Spec PhysicalNext.Repeat.Legato
open WilsonAddressedWeakCalibration
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) {k N p : ℕ}

private theorem bounds {x y : E4} {T : ℝ} (ht : 0 ≤ T) (h : ∀ i, |x i - y i| ≤ T) :
    dist x y ≤ 4*T := by
  rw [dist_eq_norm,←sq_le_sq₀ (norm_nonneg _) (by positivity),EuclideanSpace.real_norm_sq_eq]
  calc _ ≤ ∑ _ : Axis, T^2 := Finset.sum_le_sum fun i _=>sq_le_sq.mpr (by rw [abs_of_nonneg ht]; exact h i)
       _ ≤ _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat];nlinarith [sq_nonneg T]

theorem original (live : k ≤ N) (ρ : ℝ) (hr : 0 < ρ) (x : Points 2) (B : ℕ)
    (spaced : (32+4*B)*(R.family.S.a k/ρ) < dist (x 0) (x 1))
    (within : 2*(dist (x 0) (x 1) + 32*(R.family.S.a k/ρ)) <
      (R.family.side k p : ℝ)*(R.family.S.a k/ρ)) :
    let o := WilsonPositionPhysicalCellTest.site (R:=R) ρ (N,p) x
    B < separation ((R.family.S.toDepth live p).parent (o 0)) ((R.family.S.toDepth live p).parent (o 1)) := by
  let a := R.family.S.a k / ρ
  let b := lifts R (p:=p) live ρ hr x
  let y := projected R (p:=p) live ρ hr x
  let n := R.family.side k p
  have pos : 0 < a := div_pos (R.family.S.a_pos _) hr
  change (32+4*B)*a < dist (x 0) (x 1) at spaced
  change 2*(dist (x 0) (x 1)+32*a) < (n.val : ℝ)*a at within
  obtain ⟨same,near⟩ := actual R (p:=p) live ρ hr x
  have moved (i : Fin 2) : dist (y i) (x i) ≤ 16*a := (PiLp.dist_apply_le y x i).trans near
  have rev (i : Fin 2) : dist (x i) (y i) ≤ 16*a := by rw [dist_comm];exact moved i
  have above : dist (y 0) (y 1) ≤ dist (x 0) (x 1)+32*a := by
    linarith only [dist_triangle (y 0) (x 0) (y 1),dist_triangle (x 0) (x 1) (y 1),moved 0,rev 1]
  have below : dist (x 0) (x 1) ≤ dist (y 0) (y 1)+32*a := by
    linarith only [dist_triangle (x 0) (y 0) (x 1),dist_triangle (y 0) (y 1) (x 1),rev 0,moved 1]
  have counts (j : Axis) : |y 0 j-y 1 j|=a*|(((b 0-b 1) j:ℤ):ℝ)| := by
    change |ρ⁻¹*(R.family.S.a k*(b 0 j:ℝ))-ρ⁻¹*(R.family.S.a k*(b 1 j:ℝ))|=
      a*|((b 0 j-b 1 j:ℤ):ℝ)|
    rw [←abs_of_pos pos,←abs_mul]
    push_cast
    congr 1
    dsimp [a]
    ring
  have unwrapped : lift (wrap n (b 0-b 1))=b 0-b 1 := by
    apply lift_eq_iff.mpr
    refine ⟨rfl,?_⟩
    intro j
    have small : 2 * |(((b 0-b 1) j:ℤ):ℝ)| < (n.val:ℝ) := by
      apply (mul_lt_mul_iff_right₀ pos).mp
      have bill : |y 0 j-y 1 j| ≤ dist (y 0) (y 1) := by simpa only [Real.dist_eq] using PiLp.dist_apply_le (y 0) (y 1) j
      linarith only [bill,counts j,above,within]
    have lim : 2*|(b 0-b 1) j| < (n.val:ℤ) := by exact_mod_cast small
    have h₁ := le_abs_self ((b 0-b 1) j)
    have h₂ := neg_le_abs ((b 0-b 1) j)
    omega
  dsimp only
  rw [same,same]
  change _ < separation (wrap n (b 0)) (wrap n (b 1))
  by_contra! h
  have close (j : Axis) : |y 0 j-y 1 j| ≤ a*(B:ℝ) := by
    rw [counts]
    apply mul_le_mul_of_nonneg_left _ pos.le
    have bound := component_le (wrap n (b 0-b 1)) j
    rw [unwrapped] at bound
    have nat : ((b 0-b 1) j).natAbs ≤ B := by
      apply bound.trans
      simpa only [separation,←map_sub] using h
    have int : |(b 0-b 1) j| ≤ (B:ℤ) := by exact_mod_cast (Int.natCast_natAbs _ ▸ (show (((b 0-b 1) j).natAbs:ℤ) ≤ (B:ℤ) from by exact_mod_cast nat))
    exact_mod_cast int
  have metric := bounds (mul_nonneg pos.le (Nat.cast_nonneg B)) close
  linarith only [metric,below,spaced]

end YM.Integration.WilsonAddressedWeakSeparation
