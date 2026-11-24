import YM.Integration.WilsonPositionThermometerPhases

/-! Spatially integrated, normalized physical position-coupling thermometer
on every original vacuum viewer. The antiunitary choices do not change its
asymptotic coefficients. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionThermometerTest
open Function Filter Set Finset Metric MeasureTheory Lattice Wilson RG Source Extraction Table Spec
open OPE OPE.Orbits Climb Trace.Pilot Next.UVStress RG12 RG17 PhysMS PhysicalNext.Repeat.Legato
open XSpace XSpace.Normalize XSpace.Rose
open WilsonPositionThermometerPhases WilsonPositionThermometerReading
open scoped Topology ContDiff Classical BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book} (F : Final R.family f S)
variable (J : ℝ → PhysMS.tower S) {V : XSpace.Normalize.Store G} (K : XSpace.Rose.Pick V)
variable (reader : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (H : Leading F J)
    (hG : G.Simple) (X : Scaling S) (foundation : Foundation F reader)

def read (p : Viewers F) (r : ℝ) : ℝ :=
  ((Rose.test K).applyTo (raw F J p r)).re / Rose.cT K.cut G K.image

theorem unselected (r : ℝ) : read F J K none r = reading F J K r := rfl

theorem continuous (p : Viewers F) {r : ℝ} (hr : 0<r) : ContinuousOn (raw F J p r) (conf 3) := by
  apply WilsonPositionThermometerConnected.continuous_value.comp_continuousOn
  apply continuousOn_pi.mpr
  intro s
  let v (i : Fin 3) : S.Tag := ⟨6,J r 6 (leg R.family s i)⟩
  exact ((S.class_smooth (spectator F p) (spectate F p).smooth v).continuousOn).comp
    (continuous_const_smul r).continuousOn (fun _ hx => Work.A05.smul_conf hr hx)

def mass : ℝ := ∫ x : Points 3, ‖Rose.test K x‖

private theorem average {a b : Points 3 → ℂ} (ha : ContinuousOn a (conf 3)) (hb : ContinuousOn b (conf 3))
    {t : ℝ} (ht : ∀ x∈tsupport (Rose.test K),‖a x-b x‖ ≤ t) :
    ‖(Rose.test K).applyTo a-(Rose.test K).applyTo b‖ ≤ mass K*t := by
  let φ := Rose.test K
  have gi : Integrable (fun x : Points 3 => φ x) := φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have aa := φ.smearing ha
  have bb := φ.smearing hb
  change ‖(∫ x,φ x*a x)-(∫ x,φ x*b x)‖ ≤ (∫ x,‖φ x‖)*t
  rw [←integral_sub aa bb]
  apply (norm_integral_le_of_norm_le (gi.norm.mul_const t) (Eventually.of_forall (fun x => ?_))).trans
  · rw [integral_mul_const]
  · by_cases hz : φ x=0
    · simp [hz]
    · rw [←mul_sub,norm_mul]
      exact mul_le_mul_of_nonneg_left (ht x (subset_closure hz)) (norm_nonneg _)

include reader H hG X foundation in
theorem same (g : ℝ→ℝ) (hg : Coupling G g) {ε : ℝ} (he : 0<ε) (q : ℕ) :
    ∀ᶠ r in trail,∀ p v : Viewers F, |read F J K p r - read F J K v r| ≤ ε*(g r)^q := by
  let m := mass K
  let c := Rose.cT K.cut G K.image
  have hm : 0 ≤ m := integral_nonneg fun _ => norm_nonneg _
  have hc : 0 < |c| := abs_pos.mpr K.fresh.ne
  let a := ε * |c|/(m+1)
  have ha : 0<a := div_pos (mul_pos he hc) (by linarith)
  have price : m*a ≤ ε * |c| := by
    calc _ ≤ (m+1)*a := mul_le_mul_of_nonneg_right (by linarith) ha.le
         _ = _ := by dsimp only [a];field_simp [show m+1≠0 by linarith]
  let Φ := Rose.test K
  have bank := WilsonPositionThermometerPhases.same F J reader H hG X foundation Φ.hasCompactSupport Φ.tsupport_subset g hg ha q
  filter_upwards [bank,RG17.positiveLength,hg.positive] with r small hr gp p v
  have bound := average K (continuous F J p hr) (continuous F J v hr) (fun x hx => small x hx p v)
  change |((Φ.applyTo (raw F J p r)).re)/c-((Φ.applyTo (raw F J v r)).re)/c| ≤ _
  rw [←sub_div,abs_div,←Complex.sub_re,div_le_iff₀ hc]
  exact (Complex.abs_re_le_norm _).trans (bound.trans (by
    calc mass K*(a*(g r)^q) = (m*a)*(g r)^q := by dsimp only [m];ring
         _ ≤ (ε * |c|)*(g r)^q := mul_le_mul_of_nonneg_right price (pow_nonneg gp.le _)
         _ = _ := by ring))

end YM.Integration.WilsonPositionThermometerTest
