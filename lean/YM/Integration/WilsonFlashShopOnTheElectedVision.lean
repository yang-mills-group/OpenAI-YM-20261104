import YangMills.WilsonProof.NativeSupport.Commissioned259.Pose.Final
import YM.SignedWilsonExpansion.Result.Orders

noncomputable section
set_option autoImplicit false
namespace YM.Answer.ContinuumLimit.AppointedFlashRows

open Lattice RG Function Filter Wilson Integration Integration.Election Climb Extraction Trace.Pilot
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato FullVolume Spec Table Maxwell Maxwell.Free
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus MS MS.Native MS.Land MS.Fleet MS.Tide MS.Book PhysMS
open OPE OPE.Orbits FVA2 FVA2.Register FVA2.Scale FVA2.Scale.Level SignedWilsonExpansion SignedWilsonExpansion.Belle
open SignedWilsonExpansion.Belle.Path SignedWilsonExpansion.Museum SignedWilsonExpansion.Kane SignedWilsonExpansion.Kane.Tilted SignedWilsonExpansion.Camera
open Election.VaultM Election.VaultM.Till SignedWilsonExpansion.Homes SignedWilsonExpansion.Vault Vision
open Asymptotics Set FVA2.GradedFar259 FVA2.GradedFar259.Pose FVA2.GradedFar259.Comparing
open scoped BigOperators Classical Topology

universe u
variable {G : Gauge} {H : G.Simple} {ε : ℝ} {e : Axis} {O : OrderS G}
  {E : Construction.{u} H ε e O} {ξ : Extraction.Order} (V : Vision E ξ)
  (Z : WilsonPrescription G) {dial : Bool} (Q : Perspective H Z dial)

include Q
theorem measuredClock : IsEquivalent trail (V.T Z) (g0 G) :=
  Appointment.measured V Q

theorem shop : Shop V.pupil.last (V.Pre Z) Z := by
  intro d _ m _ jobs
  have clock := measuredClock V Z Q
  refine ⟨V.T Z, fun _ => 0, m, ?_, ?_, le_rfl, ?_⟩
  · intro job _ v
    let l := booth job.K trail
    have radius : Tendsto (Prod.fst : ℝ × Points job.n → ℝ) l trail := tendsto_fst
    have point : ∀ᶠ i : ℝ × Points job.n in l, i.2 ∈ job.K :=
      tendsto_snd.eventually (mem_principal.mpr Subset.rfl)
    let estimates := ((Appointment.pricesAll V).2 Z dial Q).estimates
    obtain ⟨C, _, hc⟩ := (estimates.trueLetters m l Prod.fst radius job.K
      ⟨job.cost, job.space⟩ 0 (fun _ => d) (fun _ => le_rfl) (fun _ => v)
      (fun j f => isBigO_const_const (f (v j)) one_ne_zero _)).1 false
    have raw : (fun i : ℝ × Points job.n =>
        Paper.point V.pupil.last (V.Pre Z) i.1 d job.n i.2 v -
          array (Scale.Measure.start Z.scheme Z.criterion d) i.2 m (V.T Z i.1) (stand (0 : Change G d) ∘ v))
        =O[l] fun i => (V.T Z i.1)^(m+1) := by
      apply IsBigO.of_bound C
      filter_upwards [point, hc] with i hi h
      have paid := h none ⟨i.2, job.space hi⟩ hi
      have identity : YM.Integration.Election.Frames.toView (fun _ : Fin job.n => d) d
          (fun _ => le_rfl) G v = v := by
        funext j
        apply Subtype.ext
        rfl
      simpa [Life, orchestra, Paper.point, walk, Lamplight, mote, array, identity,
        stand, Function.comp_def, norm_pow, Real.norm_eq_abs] using paid
    apply raw.trans
    have small : (fun r => g0 G r ^ (m + 1)) =O[trail] (fun r => g0 G r ^ m) := by
      apply IsBigO.of_bound'
      filter_upwards [g0_pos H, (g0_zero H).eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))] with r hr hs
      rw [Real.norm_of_nonneg (pow_nonneg hr.le (m+1)),
        Real.norm_of_nonneg (pow_nonneg hr.le m), pow_succ]
      exact mul_le_of_le_one_right (pow_nonneg hr.le _) hs.le
    exact ((clock.isBigO.pow (m+1)).trans small).comp_tendsto radius
  · simp only [map_zero] <;> exact tendsto_const_nhds
  · exact (isEquivalent_iff_tendsto_one ((g0_pos H).mono fun _ hr => hr.ne')).1 clock

end YM.Answer.ContinuumLimit.AppointedFlashRows
