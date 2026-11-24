import YM.Integration.WilsonPositionPhaseProfile
import YM.Integration.WilsonPositionHomogeneousComparison

/-! Test the true homogeneous measuring hierarchy against a full signed configuration profile. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionPhaseProfileTest
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Source Extraction Table Spec OPE OPE.Orbits Climb RG17
  Trace.Pilot PhysMS Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register PhysicalNext.Repeat.Legato
open scoped Topology ContDiff Classical BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
  (F : Final R.family f S) (J : ℝ → PhysMS.tower S) (Z : WilsonPrescription G)
  {n : ℕ} {d : Caps n}

/-- Physical signed joint reading, including the original unselected viewer. -/
def reading (p : Viewers F) (φ : Test n) (v : MaxwellSlots R.family d) (r : ℝ) : ℂ :=
  φ.applyTo (measured F p (WilsonPositionHomogeneousFrame.homogeneous F J Z r) v r)

theorem smooth (p : Viewers F) (v : MaxwellSlots R.family d) {r : ℝ} (rp : 0 < r) :
    ContinuousOn (measured F p (WilsonPositionHomogeneousFrame.homogeneous F J Z r) v r) (conf n) := by
  let V (i : Fin n) : S.Tag := ⟨d i, WilsonPositionHomogeneousFrame.homogeneous F J Z r (d i) (v i)⟩
  apply (S.class_smooth (spectator F p) (spectate F p).smooth V).continuousOn.comp
  · fun_prop
  · intro x hx
    exact Work.A05.smul_conf rp hx

def mass (φ : Test n) : ℝ := ∫ x : Points n, ‖φ x‖

theorem price (φ : Test n) {u w : Points n → ℂ} {a : ℝ}
    (hu : Integrable (fun x => φ x * u x)) (hw : Integrable (fun x => φ x * w x))
    (close : ∀ x ∈ tsupport (φ : Points n → ℂ), ‖u x-w x‖ ≤ a) :
    ‖φ.applyTo u-φ.applyTo w‖ ≤ mass φ * a := by
  unfold Test.applyTo mass
  rw [← integral_sub hu hw]
  have bank : Integrable (fun x : Points n => φ x) :=
    φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  apply (norm_integral_le_of_norm_le (bank.norm.mul_const a) (Eventually.of_forall ?_)).trans_eq
    (integral_mul_const _ _)
  intro x
  rw [← mul_sub, norm_mul]
  by_cases hx : x ∈ tsupport (φ : Points n → ℂ)
  · exact mul_le_mul_of_nonneg_left (close x hx) (norm_nonneg _)
  · rw [image_eq_zero_of_notMem_tsupport hx, norm_zero, zero_mul, zero_mul]

variable (reader : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
  (lead : Leading F J) {Y : (Bel R.family.book).Hierarchy}
  (paid : ∀ d : ℕ, ∀ᶠ r in trail, PhysMS.Frame.obedient F Y (J r) d)
  (hG : G.Simple) (X : Scaling S) (foundation : Foundation F reader)

include reader lead paid hG X foundation in
theorem phases (φ : Test n) (v : MaxwellSlots R.family d) (g : ℝ → ℝ) (hg : Coupling G g)
    {ε : ℝ} (he : 0 < ε) (N : ℕ) :
    ∀ᶠ r in trail, ∀ p q : Viewers F,
      ‖reading F J Z p φ v r - reading F J Z q φ v r‖ ≤ ε * g r ^ N := by
  let A := mass φ + 1
  have hm : 0 ≤ mass φ := integral_nonneg fun _ => norm_nonneg _
  have ap : 0 < A := add_pos_of_nonneg_of_pos hm one_pos
  let moving (r : ℝ) (i : Fin n) := WilsonPositionPrescribedLift.field F J Z.store (d i) r
    (WilsonPositionHomogeneousFrame.change F J Z (d i) r (v i))
  have all := WilsonPositionPhaseProfile.moving F J reader lead hG X foundation moving v
    (fun i => WilsonPositionHomogeneousLeading.field F J Z lead paid hG (d i) (v i))
    φ.hasCompactSupport φ.tsupport_subset g hg (div_pos he ap) N
  filter_upwards [all,RG17.positiveLength,hg.positive] with r bank rp gp p q
  have paidφ := price φ
    (φ.smearing (smooth F J Z p v rp)) (φ.smearing (smooth F J Z q v rp))
    (a:=ε/A * g r ^ N) (fun x hx => bank x hx p q)
  calc
    _ ≤ mass φ * (ε/A * g r ^ N) := paidφ
    _ ≤ A * (ε/A * g r ^ N) :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
        (mul_nonneg (div_pos he ap).le (pow_nonneg gp.le _))
    _ = _ := by field_simp [ap.ne']

end YM.Integration.WilsonPositionPhaseProfileTest

