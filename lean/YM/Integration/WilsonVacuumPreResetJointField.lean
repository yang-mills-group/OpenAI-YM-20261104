import YM.Integration.WilsonHeldKineticPathTaylor
import YM.RG01Estimate.Nodules

/-! The coarse interior and the relative fine increments on the same original
forest form one chart. The exterior and the frozen fine variables are held. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetJointField
open Function Lattice Wilson RG Tree Pressure Gauge Precision
open ConnectedActivityE6 Coat Control Blaze Push Push.Uniform Push.AbsoluteSums
open AnalyticNext.QuarticMatch.Estimate RG01.Sounder Logfee
open Work.F03 PhysicalNext PhysicalNext.Repeat Lapis Bid
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}

abbrev Arguments (G : Gauge) (c f : Side) := Positions (Primary c G) × Directions G f

def walls (P : Finset (Bond c)) (V : Config G c) (b : Positions (Primary c G)) : Config G c :=
  fun e => if e ∈ P then Boulevard.actual b e else V e

def field (P : Finset (Bond c)) (X : Coat T F) (z : Arguments G c f) : Config G f :=
  ({ X with V := walls P X.V z.1 } : Coat T F).input z.2

/-- On an active bond, the relative fine exponential multiplies the replicated
coarse link on the left. The genuine draped frozen field includes every trunk. -/
theorem at_bond (P : Finset (Bond c)) (X : Coat T F) (z : Arguments G c f) (e : Bond f) :
    field P X z e = if X.Hot e then
      G.lieExp (z.2 e) * replica S.ratio (walls P X.V z.1) e else F.drape X.Y e := by
  let X' : Coat T F := { X with V := walls P X.V z.1 }
  by_cases h : X.Hot e
  · rw [if_pos h]
    exact X'.viewing z.2 e h
  · rw [if_neg h]
    exact X'.dormant z.2 e h

theorem original (P : Finset (Bond c)) (X : Coat T F) (z : Arguments G c f)
    (inside : ∀ e ∈ P, Boulevard.actual z.1 e = X.V e) : field P X z = X.input z.2 := by
  have h : walls P X.V z.1 = X.V := by
    funext e
    by_cases h : e ∈ P
    · simpa only [walls, if_pos h] using inside e h
    · simp [walls, h]
  simp only [field, h]

private def crown (G : Gauge) (j : ℕ) (M : ℝ) := ample G * (1 + |M| * (unitPrice G j).C)^j

private theorem exponential {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (j : ℕ) (L : E →L[ℝ] G.Color) {M : ℝ} (h : ‖L‖ ≤ M) (z : E) :
    Allows j (fun y => G.mat (G.lieExp (L y))) z (crown G j M) := by
  refine ⟨(G.exp_jet.comp L.contDiff).contDiffAt, fun i hi => ?_⟩
  have hz := (unitPrice G j).used
  have hc := ample_back G
  have hM : 0 ≤ M := (norm_nonneg _).trans h
  refine (endless L z j i hi).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by linarith)
  refine (pow_le_pow_left₀ (by positivity) (show _ ≤ 1 + |M| * (unitPrice G j).C from ?_) i).trans
    (pow_le_pow_right₀ (by exact le_add_of_nonneg_right (by positivity)) hi)
  rw [abs_of_nonneg hM, mul_comm _ ‖L‖]
  exact (mul_le_mul_of_nonneg_right h (by linarith)).trans (le_add_of_nonneg_left (by norm_num))

def unitFee (G : Gauge) (j : ℕ) := max (crown G j 1) (max (crown G j (shade G)) ‖(1 : G.Mat)‖)
def linkFee (G : Gauge) (j : ℕ) := max (unitFee G j) (2^j * unitFee G j * unitFee G j)

/-- The link price is independent of the period, the chosen patch, and the
values on its exterior, and controls the mixed coarse/fine derivatives. -/
theorem links (P : Finset (Bond c)) (X : Coat T F) (j : ℕ) (z : Arguments G c f) (e : Bond f) :
    Allows j (fun a => G.mat (field P X a e)) z (linkFee G j) := by
  let E := Positions (Primary c G)
  let U := Directions G f
  let D := unitFee G j
  have hf : crown G j 1 ≤ D := le_max_left _ _
  have hp : crown G j (shade G) ≤ D := (le_max_left _ _).trans (le_max_right _ _)
  have hv : ‖(1 : G.Mat)‖ ≤ D := (le_max_right _ _).trans (le_max_right _ _)
  have active (a : Bond f) : Allows j (fun q : E × U => G.mat (G.lieExp (q.2 a))) z D := by
    let L := (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Bond f => G.Color) a) ∘L
      ContinuousLinearMap.snd ℝ E U
    have norm : ‖L‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => by
      rw [one_mul]
      exact (norm_le_pi_norm y.2 a).trans (norm_snd_le _)
    exact (exponential j L norm z).mono hf
  have fixed (v : G.El) : Allows j (fun _ : E × U => G.mat v) z D :=
    (allows_const z (unit_pay v).le).mono hv
  have moving (a : Bond c) : Allows j (fun q : E × U => G.mat (Boulevard.actual q.1 a)) z D := by
    unfold Boulevard.actual
    simp_rw [Work.F03.represent_link]
    let L := (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Exterior.Body 1 c => G.Color)
      (a.1, Exterior.coord a.2)) ∘L (tint G (Exterior.Body 1 c)).toContinuousLinearMap ∘L ContinuousLinearMap.fst ℝ E U
    have norm : ‖L‖ ≤ shade G := ContinuousLinearMap.opNorm_le_bound _ (shade_pos G).le fun y =>
      (norm_le_pi_norm (tint G _ y.1) _).trans ((tint_le _).trans
        (mul_le_mul_of_nonneg_left (norm_fst_le _) (shade_pos G).le))
    exact (exponential j L norm z).mono hp
  simp_rw [at_bond P X]
  by_cases h : X.Hot e
  · simp only [if_pos h]
    have right : Allows j (fun q : E × U => G.mat (replica S.ratio (walls P X.V q.1) e)) z D := by
      unfold replica
      split
      · exact fixed 1
      · unfold walls
        split
        · exact moving _
        · exact fixed _
    exact ((active e).times right).mono (le_max_right _ _)
  · simp only [if_neg h]
    exact (fixed (F.drape X.Y e)).mono (show D ≤ linkFee G j from le_max_left _ _)

end YM.Integration.WilsonVacuumPreResetJointField
