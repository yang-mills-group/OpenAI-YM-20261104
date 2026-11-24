import YM.Integration.WilsonSeparatedDiagnosticFrames
import YM.OPE.Eye.Cloud
import YM.RG17.Profile

/-! The original screened lattice rounding on the preselected fine mesh,
uniform on all positions at diagnostic separation r. It avoids imposing
coordinatewise noncoincidence on the continuum profiles. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedProfileGrid
open Filter Function Set Finset Lattice Spec OPE OPE.Log OPE.Orbits Trace.Pilot SharedIntrinsicWilsonGrid
open scoped Classical BigOperators Topology
variable {G : Gauge} {C : Family G} {n D : ℕ}

def sites (S:Schedule) (j:ℕ) (r:ℝ) (X:Points n) : Fin n → Cover :=
  Cloud.grid ∅ (S.a j) (RG17.posed r X) (fun _ _=>0)

def shape (S:Schedule) (j:ℕ) (r:ℝ) (X:Points n) : Points n :=
  r⁻¹ • points (S.gridPoint j ∘ sites S j r X)

theorem screen (S:Schedule) (j:ℕ) (r:ℝ) (X:Points n) :
    Screen (S.gridPoint j ∘ sites S j r X) :=
  Cloud.screened ∅ (S.a j) (S.a_pos j) (RG17.posed r X) (fun _ _=>0)

theorem at_shape (S:Schedule) (j:ℕ) {r:ℝ} (rp:0<r) (X:Points n) :
    RG17.posed r (shape S j r X) = S.gridPoint j ∘ sites S j r X := by
  funext i
  change r • (r⁻¹ • (S.gridPoint j (sites S j r X i)))=_
  rw [smul_smul,mul_inv_cancel₀ rp.ne',one_smul]
  rfl

private def toll (n:ℕ) : ℝ := (4*n:ℝ)*(Cloud.count (Fin n) ∅:ℝ)

private theorem absolute (S:Schedule) (j:ℕ) (r:ℝ) (X:Points n) :
    ‖points (S.gridPoint j ∘ sites S j r X)-r • X‖ ≤ toll n*S.a j := by
  let E := points (S.gridPoint j ∘ sites S j r X)-r • X
  let a := S.a j*((Cloud.count (Fin n) ∅):ℝ)
  have ap : 0<a := mul_pos (S.a_pos _) (by exact_mod_cast (Cloud.count_pos (I:=Fin n) ∅))
  have bound (i:Fin n×Axis) : |(Points.flatten E) i| ≤ a :=
    Cloud.close_zero ∅ (S.a j) (S.a_pos j) (RG17.posed r X) i.1 i.2
  have enough : ‖E‖ ≤ (4*n:ℝ)*a := by
    rw [←sq_le_sq₀ (norm_nonneg _) (by positivity),←Points.flatten.norm_map E,EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ _ : Fin n×Axis,a^2 := Finset.sum_le_sum fun i _=>sq_le_sq.mpr (by rw [abs_of_pos ap]; exact bound i)
      _ ≤ _ := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul,
          Nat.cast_mul,Nat.cast_ofNat]
        rcases Nat.eq_zero_or_pos n with h|h
        · rw [h]; simp
        change (n:ℝ)*4*a^2 ≤ (4*n*a)^2
        rw [mul_pow (4*(n:ℝ)) a]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have hn : (1:ℝ)≤n := by exact_mod_cast h
        nlinarith
  exact enough.trans_eq (by dsimp only [toll,a]; ring)

/-- The proportional displacement in rescaled coordinates has every power
below c−1, where c is the genuine fine height of the actual shared plan. -/
theorem fine {N p:ℕ} (P : Plan C D N p) {θ:ℝ} (fit : 1+θ<P.c) :
    ∀ᶠ r in trail, ∀ X:Points n,‖shape C.S (P.j r) r X-X‖ ≤ r^θ := by
  let ht := PhysMS.to_log_zoom
  have hi := (PhysMS.length_rate.rpow (1+θ)).overtakes
    ((RateLE.const (toll n) ht).mul (P.fine.mesh.pays ht)) ht (by
      simp only [zero_add,mul_neg,mul_one]
      linarith only [fit])
  filter_upwards [hi,PhysMS.length_rate.pos] with r paid pos X
  change 0<r at pos
  have margin : toll n*C.S.a (P.j r) ≤ r*r^θ := by
    simpa only [id_eq,Real.rpow_add pos,Real.rpow_one] using paid.le
  calc
    _ = ‖r⁻¹ • (points (C.S.gridPoint (P.j r) ∘ sites C.S (P.j r) r X)-r • X)‖ := by
      rw [smul_sub,smul_smul,inv_mul_cancel₀ pos.ne',one_smul]; rfl
    _ ≤ r⁻¹*(r*r^θ) := by
      rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr pos).le]
      exact mul_le_mul_of_nonneg_left ((absolute C.S (P.j r) r X).trans margin) (inv_pos.mpr pos).le
    _ = _ := inv_mul_cancel_left₀ pos.ne' _

end YM.Integration.WilsonSeparatedProfileGrid
