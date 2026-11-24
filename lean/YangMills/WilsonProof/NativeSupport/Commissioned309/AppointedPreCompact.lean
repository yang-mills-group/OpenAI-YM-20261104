import YM.GradedFar.Elected.Voters
import YM.SignedWilsonExpansion.Result.Orders

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 12000
noncomputable section
namespace YM.FVA2.GradedFar.Appointed1859PreAmple
open YM YM.Integration YM.Integration.Election YM.Answer.ContinuumLimit YM.Answer.ContinuumLimit.Vision
open YM.Spec YM.FVA2 YM.FVA2.Register YM.PhysMS YM.Trace.Pilot
open YM.XSpace YM.XSpace.Normalize YM.XSpace.Structure1 YM.XSpace.Cirrus YM.XSpace.Rose
open YM.MS YM.MS.Native YM.MS.Book YM.MS.Menus YM.MS.Tide YM.MS.Theater YM.MS.Fleet YM.MS.Land
open YM.PhysicalNext.Repeat.Legato YM.RG17 YM.Climb YM.Maxwell
open YM.SignedWilsonExpansion YM.SignedWilsonExpansion.Dancer YM.SignedWilsonExpansion.Kane YM.SignedWilsonExpansion.Kane.Tilted
open YM.SignedWilsonExpansion.Belfry YM.SignedWilsonExpansion.Belfry.Classroom YM.SignedWilsonExpansion.Belfry.ScaleFits
open YM.SignedWilsonExpansion.Belle YM.SignedWilsonExpansion.Belle.Path YM.SignedWilsonExpansion.Belle.Buffet
open FVA2.Scale FVA2.Reg FVA2.Dframe O O.Score O.Enh O.Canon Jury Facets Growth Pose Moving Matrix
open MS.Book.Program Dancer Commission Belle Belle.Path Belle.Buffet Future Generator Generator.Drive
open Function Filter Set Asymptotics PowerSeries
open scoped Topology BigOperators Classical ContDiff
universe u
variable {G : Gauge} {H : G.Simple} {ε : ℝ} {e : Axis} {O : OrderS G}
  {E : Construction.{u} H ε e O} {f : Extraction.Order}
  (V : Vision E f) (Z : YM.FVA2.Register.WilsonPrescription G) (Q : Perspective H Z true)
local notation "W" => Elected.Wframe Z V.pupil.last V.pupil.J
local notation "Θ" => V.T Z
local notation "U" => V.pupil.last

include Q in
theorem heater : Tendsto (fun r => Θ r / gYM G r) trail (𝓝 1) := by
  have h := (Vision.marks_the_data Z V Q).clock
  exact relative_running H Θ h.positive h.running

include Q in
theorem heaterPower (q : ℕ) :
    (fun r => Θ r ^ (q+1)) =O[trail] (fun r => gYM G r ^ q) := by
  apply IsBigO.of_bound ((2:ℝ)^q)
  filter_upwards [paid_reading H Θ (heater V Z Q)] with r h
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, abs_pow, abs_of_pos h.1, pow_succ]
  calc |Θ r|^q * |Θ r| ≤ (2 * gYM G r)^q * 1 :=
      mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) h.2.2.2 q) h.2.2.1
        (abs_nonneg _) (pow_nonneg (mul_nonneg (by norm_num) h.1.le) _)
    _ = (2:ℝ)^q * gYM G r ^ q := by rw [mul_one,mul_pow]

include Q in
theorem confirmed {n d : ℕ} (v : Tags G d n) (K : Set (Points n))
    (hc : IsCompact K) (hx : K ⊆ conf n) (q : ℕ) :
    Pose.Confirmed Z (Physical.familyPoint U W d) q q Θ (fun _ => 0) K v := by
  let label : PUnit → ℝ → Tags G d n := fun _ _ => v
  have pay : ∀ a : PUnit, ∀ k : Fin n, SeatsW.Salary ℂ trail 1 (fun i => label a i k) :=
    fun _ _ => SeatsW.income (fun _ => tendsto_const_nhds)
  have sale := (V.pricedLines Q).linearizations q trail id tendsto_id K ⟨hc,hx⟩
    (.cup PUnit.unit) label pay false
  obtain ⟨C,_,hs⟩ := sale.regular.1
  apply Pose.Terms.mono (hy := heaterPower V Z Q q)
  apply Pose.Terms.of_be
  refine ⟨C,?_⟩
  filter_upwards [hs] with r hr
  intro x
  have h := hr none x.val x.property
  change ‖(Physical.familyPoint U W d r n x.val) v -
    (WilsonCoeffUV.Mer.Xa.MarqueQ.Crops.calcT (Θ r : ℂ) q)
      (Reg.Point.story (Scale.Jury.fxt (Scale.Measure.start Z.scheme Z.criterion d) x.val) v)‖ ≤
        C * ‖Θ r ^ (q+1)‖ at h
  rw [WilsonCoeffUV.Mer.Xa.MarqueQ.Crops.timed] at h
  have hzero : stand (0 : Change G d) ∘ v = v := by
    funext i
    simp [stand]
  simp only [hzero]
  simpa [GradedFar.crop, Pose.line, Pose.Bbook, Reg.Point.story, PowerSeries.coeff_mk, mul_comm] using h

include Q in
theorem latest : Books.Latest Z (Physical.familyPoint U W) := by
  intro d n p v K hc hx
  let k := max 2 (p+1)
  refine ⟨k,k,Θ,(fun _ => 0),(fun _ => 0), le_max_left ..,le_max_right ..,le_rfl,
    heater V Z Q,?_,?_,?_,?_,confirmed V Z Q v K hc hx k⟩
  · simpa only [map_zero] using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0:MoveSpace G 6)) trail (𝓝 0))
  · simpa only [map_zero] using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0:MoveSpace G d)) trail (𝓝 0))
  · constructor
    · intro i
      let w := (Z.store.survey 6).scope i
      exact confirmed V Z Q w.p (tsupport w.t) w.t.hasCompactSupport w.t.tsupport_subset k
    · intro s
      exact confirmed V Z Q (missing (tag G) s) (tsupport (Rose.test Z.criterion))
        (Rose.test Z.criterion).hasCompactSupport (Rose.test Z.criterion).tsupport_subset k
  · intro i
    let w := (Z.store.survey d).scope i
    exact confirmed V Z Q w.p (tsupport w.t) w.t.hasCompactSupport w.t.tsupport_subset k

end YM.FVA2.GradedFar.Appointed1859PreAmple

