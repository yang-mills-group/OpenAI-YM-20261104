import YM.Integration.WilsonPositionScaleLawMeasuredTestMass
import YM.Integration.WilsonViewerPositionSeries
/-! The true smeared F11 archive error retains its original integral.
Its independently issued clipped field is exactly the sum of its true
outlook coefficient integrals on the same nominated physical pupil. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonNestedReportedCharacterCurrentBayQ343MSExamFarArchiveIntegral
open Function Filter Set Finset MeasureTheory Spec Extraction Table PhysicalNext.Repeat.Legato
open OPE OPE.Orbits Climb RG17 PhysMS Trace.Pilot Maxwell XSpace XSpace.Normalize
open FVA2 FVA2.Register FVA2.Scale FVA2.Arrival MS MS.Land MS.Fleet
open Position Position.Axes
open WilsonPositionScaleLawMeasuredSection (clipped)
open WilsonPositionScaleLawMeasuredExperiment (mass)
open scoped Topology BigOperators Classical
variable {G:Gauge}(Z:WilsonPrescription G){simple:G.Simple}
    (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))){σ:Prescription (Press.portDeck G)}
    {dial:Bool}(matched:Main.Match Z simple M σ dial)(ν:ℝ)
    {R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)

theorem sourced {n:ℕ}(φ:Test n)(A:Points n→ℂ)(legal:ContinuousOn A (conf n)):
    Integrable (fun x=>φ x*A x):=by
  have full:Continuous (fun x=>φ x*A x):=by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases live:x∈conf n
    · exact φ.continuous.continuousAt.mul (legal.continuousAt ((conf_open n).mem_nhds live))
    · have away:x∉tsupport (φ:Points n→ℂ):=fun h=>live (φ.tsupport_subset h)
      have free:∀ᶠy in 𝓝 x,y∉tsupport (φ:Points n→ℂ):=(isClosed_tsupport _).isOpen_compl.mem_nhds away
      have vacant:(fun y=>φ y*A y)=ᶠ[𝓝 x] (fun _=>0):=free.mono fun y hy=>by
        have zero:φ y=0:=by
          by_contra hn
          exact hy (subset_tsupport _ hn)
        change φ y*A y=0
        rw [zero,zero_mul]
      change Tendsto _ (𝓝 x) (𝓝 (φ x*A x))
      rw [vacant.eq_of_nhds]
      exact tendsto_const_nhds.congr' vacant.symm
  exact full.integrable_of_hasCompactSupport φ.hasCompactSupport.mul_right

theorem charged {n:ℕ}(φ:Test n){A B:Points n→ℂ}(a:ContinuousOn A (conf n))(b:ContinuousOn B (conf n))
    (C:ℝ)(small:∀x∈tsupport (φ:Points n→ℂ),‖A x-B x‖≤C):
    ‖φ.applyTo A-φ.applyTo B‖ ≤ mass φ*C:=by
  have rent:Integrable (fun x:Points n=>φ x):=φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  change ‖(∫x,φ x*A x)-∫x,φ x*B x‖≤(∫x,‖φ x‖)*C
  rw [←integral_sub (sourced φ A a) (sourced φ B b)]
  apply (norm_integral_le_of_norm_le (rent.norm.mul_const C) (Eventually.of_forall (fun x=>?_))).trans
  · rw [integral_mul_const]
  · by_cases absent:φ x=0
    · simp [absent]
    · rw [←mul_sub,norm_mul]
      exact mul_le_mul_of_nonneg_left (small x (subset_tsupport _ absent)) (norm_nonneg _)

def form {d n:ℕ}(q:ℕ)(a:ℝ)(v:Fin n→Sec G d)(y:Points n):ℂ:=
  ∑k∈Finset.range (q+1),(a:ℂ)^k*Jury.fxt (Measure.outlook Z.scheme Z.criterion d) y k v

include matched ν in
theorem opening {d n:ℕ}(k:ℕ)(v:Fin n→Sec G d):
    ContinuousOn (fun y:Points n=>Jury.fxt (Measure.outlook Z.scheme Z.criterion d) y k v) (conf n):=
  (WilsonPositionScaleLawMeasuredSection.enrolled Z M matched ν d).light n k v

include matched ν in
theorem legal {d n:ℕ}(q:ℕ)(a:ℝ)(v:Fin n→Sec G d):ContinuousOn (form Z q a v) (conf n):=by
  unfold form
  exact continuousOn_finsetSum _ (fun k _=>continuousOn_const.mul (opening Z M matched ν k v))

include matched in
theorem original {d n:ℕ}(q:ℕ)(a:ℝ)(φ:Test n)(v:Fin n→Sec G d):
    clipped Z M ν d q a n φ v=φ.applyTo (form Z q a v):=by
  rw [WilsonPositionScaleLawMeasuredSection.value]
  unfold Test.applyTo form
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k _
    rw [(WilsonPositionScaleLawMeasuredSection.enrolled Z M matched ν d).exact n k φ v]
    change _*(∫x,φ x*Jury.fxt _ x k v)=∫x,φ x*(_*Jury.fxt _ x k v)
    simp_rw [show ∀x:Points n,φ x*((a:ℂ)^k*Jury.fxt (Measure.outlook Z.scheme Z.criterion d) x k v)=
      (a:ℂ)^k*(φ x*Jury.fxt (Measure.outlook Z.scheme Z.criterion d) x k v) from fun _=>by ring]
    rw [integral_const_mul]
  · intro k _
    exact sourced φ _ (continuousOn_const.mul (opening Z M matched ν k v))

theorem physical {n:ℕ}{d:Caps n}(H:tower S)(v:MaxwellSlots R.family d){r:ℝ}(pos:0<r)(view:Viewers F):
    ContinuousOn (measured F view H v r) (conf n):=by
  let V (i:Fin n):S.Tag:=⟨d i,H (d i) (v i)⟩
  apply ((S.class_smooth (spectator F view) (spectate F view).smooth V).continuousOn).comp
  · change ContinuousOn (fun z:Points n=>r • z) (conf n)
    fun_prop
  · intro x ok;exact Work.A05.smul_conf pos ok
end YM.Integration.WilsonNestedReportedCharacterCurrentBayQ343MSExamFarArchiveIntegral
end
