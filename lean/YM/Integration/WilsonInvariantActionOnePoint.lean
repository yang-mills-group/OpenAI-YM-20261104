import YM.Integration.WilsonInvariantActionScale
import YM.PhysMS.Frame.Journey
import YM.OPE.Eye.Views

/-! The true rotation-invariant action in the original Wilson calibration.
The exact Ward equality fixes its whole field up to a constant multiple
of the physical unit, with the physical length to the fourth power. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonInvariantActionOnePoint
open Filter Function Set Table Spec Climb Spin Trace.Pilot Trace.Over TraceExtension PhysMS
open OPE OPE.Orbits MeasureTheory
open scoped Classical Topology
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
  (F : Final C f S) (J : ℝ→tower S)

theorem resolved (simple : G.Simple) {P : ℝ→change S 4} {δ g : ℝ→ℝ}
    (same : ∀ᶠr in trail,J r 4=P r) (cal : TendC F P δ) (coupling : Coupling G g) :
    ∃c:ℂ,∀ᶠr in trail,J r 4 (stepField C)=(r^4/(4*δ r)) • (center F - c • S.unit 4) := by
  obtain ⟨c,raw⟩:=cal.centered
  refine ⟨c,?_⟩
  filter_upwards [raw,same,(Trace.Link.logfit F simple g δ P coupling cal).eventually_ne (by norm_num : (-1:ℝ)≠0)]
    with r hJ hj nonzero
  have h : 4*δ r≠0:=right_ne_zero_of_mul nonzero
  apply smul_right_injective (S.Field 4) h
  change (4*δ r) • (J r 4 (stepField C))=(4*δ r) • ((r^4/(4*δ r)) • (center F - c • S.unit 4))
  rw [smul_smul,show (4*δ r)*(r^4/(4*δ r))=r^4 by field_simp [right_ne_zero_of_mul h],hj,smul_sub,eq_sub_iff_add_eq]
  exact hJ.symm

private theorem test_constant (φ : Test 1) (s : ℝ) (z : ℂ) :
    φ.applyTo (fun _=>(s:ℂ)*z)=(s:ℂ)*φ.applyTo (fun _=>z) := by
  unfold Test.applyTo
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  ring

theorem tested (simple : G.Simple) {P : ℝ→change S 4} {δ g : ℝ→ℝ}
    (same : ∀ᶠr in trail,J r 4=P r) (cal : TendC F P δ) (coupling : Coupling G g)
    (p : Viewers F) (φ : Test 1) (q : ℕ) :
    Tendsto (fun r=>φ.applyTo (fun x=>S.classMoment (spectator F p) (fun _=>4) (r•x)
      (fun _=>J r 4 (stepField C))) / (g r:ℂ)^q) trail (𝓝 0) := by
  obtain ⟨c,values⟩:=resolved F J simple same cal coupling
  let fixed:=center F - c • S.unit 4
  let z:=euclideanVEV S (spectator F p) fixed
  have flat:=WilsonInvariantActionScale.flat simple coupling (Trace.Link.logfit F simple g δ P coupling cal) q
  have read:= (Complex.continuous_ofReal.continuousAt.tendsto.comp flat).mul_const (φ.applyTo (fun _=>z))
  rw [Complex.ofReal_zero,zero_mul] at read
  apply read.congr'
  filter_upwards [values] with r value
  have points (x:Points 1) : S.classMoment (spectator F p) (fun _=>4) (r•x)
      (fun _=>J r 4 (stepField C)) = (r^4/(4*δ r):ℝ) • z := by
    change S.useAt (spectator F p) (r•x) (fun _=>⟨4,J r 4 (stepField C)⟩)=_
    rw [vev_coordinates (spectate F p).translations,value,
        show (r^4/(4*δ r)) • (center F-c • S.unit 4)=((r^4/(4*δ r):ℝ):ℂ) • fixed from Complex.coe_smul ..,
        vev_linear.map_smul]
    rfl
  simp_rw [points,Complex.real_smul]
  rw [test_constant]
  change (((r^4/(4*δ r))/(g r)^q:ℝ):ℂ)*φ.applyTo (fun _=>z)=_
  push_cast
  ring

end YM.Integration.WilsonInvariantActionOnePoint
