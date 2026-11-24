import YM.Integration.WilsonMovingCompactTransfer
import YM.Integration.WilsonRelativeChildRoute

/-! The ancestor of an actual fine observation on the same lifted period.
Subtracting the genuine signed residue also works across the torus seam. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportCellProjection
open Function Finset Set Metric Lattice Extraction FullVolume
open scoped Classical BigOperators

def ancestor {c f : Side} (g : Ratio c f) (u : Cover) : Cover :=
  u-lift (g.residue (wrap f u))

theorem exact_site {c f : Side} (g : Ratio c f) (u : Cover) :
    wrap f (ancestor g u)=g.embed (g.parent (wrap f u)) := by
  unfold ancestor; rw [map_sub,sub_eq_iff_eq_add]; exact (g.unpack_at _).symm

theorem coordinates (S : Schedule) {k N : ℕ} (h : k≤N) (p : ℕ)
    {n : ℕ} (z : Positions n) :
    ‖tag (S.a N) (ancestor (S.toDepth h p) ∘ z) - tag (S.a N) z‖ ≤ (4*n:ℝ)*S.a k := by
  let g := S.toDepth h p
  let E := tag (S.a N) (ancestor g ∘ z) - tag (S.a N) z
  have ha := S.a_pos N; have hb := S.a_pos k
  have coord (i : Fin n×Axis) : |(Points.flatten E) i| ≤ S.a k := by
    let u := lift (g.residue (wrap _ (z i.1))) i.2
    have room := lift_centers (g.residue (wrap _ (z i.1))) i.2
    have ui : |u|≤(g.count.val:ℤ) := abs_le.mpr ⟨by dsimp only [u]; omega,by dsimp only [u]; omega⟩
    have bound : |(u:ℝ)|≤(g.count.val:ℝ) := by exact_mod_cast ui
    change |S.a N*((z i.1 i.2-u:ℤ):ℝ)-S.a N*(z i.1 i.2:ℝ)|≤S.a k
    rw [Int.cast_sub, show S.a N*((z i.1 i.2:ℝ)-(u:ℝ))-S.a N*(z i.1 i.2:ℝ) =
        -(S.a N*(u:ℝ)) by ring, abs_neg,abs_mul,abs_of_pos ha]
    calc S.a N*|(u:ℝ)| ≤ S.a N*(g.count.val:ℝ) := mul_le_mul_of_nonneg_left bound ha.le
         _ = S.a k := by rw [← S.embeds_scale g]
  change ‖E‖ ≤ (4*n:ℝ)*S.a k
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity),← (Points.flatten.norm_map E),EuclideanSpace.real_norm_sq_eq]
  calc _ ≤ ∑ _i:Fin n×Axis,(S.a k)^2 := sum_le_sum fun i _=>sq_le_sq.mpr (by rw [abs_of_pos hb]; exact coord i)
       _ ≤ _ := by
         simp only [sum_const, card_univ,Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat]
         rcases Nat.eq_zero_or_pos n with he | he
         · rw [he]; simp
         rw [mul_pow]; apply mul_le_mul_of_nonneg_right _ (by positivity)
         have h1 : (1:ℝ)≤n := by exact_mod_cast he
         nlinarith

theorem relative (S : Schedule) {k N : ℕ} (h : k≤N) (p : ℕ)
    {n : ℕ} (z : Positions n) {r : ℝ} (hr : 0<r) :
    ‖r⁻¹ • tag (S.a N) (ancestor (S.toDepth h p) ∘ z) - r⁻¹ • tag (S.a N) z‖ ≤ (4*n:ℝ)*S.a k/r := by
  rw [←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr),div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (coordinates S h p z) (inv_nonneg.mpr hr.le)

end YM.Integration.WilsonReportCellProjection
