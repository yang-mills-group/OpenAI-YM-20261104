import YM.Integration.WilsonFlashFiniteInputBalls
import YM.Integration.WilsonFlashOnThePublishedBasisRows
import YM.GradedFar.Round.G9

set_option quotPrecheck false
noncomputable section
namespace YM.FVA2.GradedFar.AppointedFlashNumerator
open Filter Function Real Set
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open OPE OPE.Orbits O O.Score O.Enh Scale Dframe YM.FVA2.GradedFar259 YM.FVA2.GradedFar259.Comparing
open Continuation Continuation.Window
open YM.Answer.ContinuumLimit YM.Integration
open scoped Topology BigOperators Classical
universe u
variable (g : YangMills.GaugeGroup) (hg : g.IsSimple) (dates : ℕ → ℕ) (strictDates : StrictMono dates)
private abbrev issuedDatum := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
private abbrev selectedVision := WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)
private abbrev electedPerspective := WilsonGraphPaperPublication.perspective.{u} g hg
private abbrev filedFrame := Elected.Hframe (issuedDatum g hg) (selectedVision.{u} g hg dates strictDates).pupil.last (selectedVision.{u} g hg dates strictDates).pupil.J

theorem onWindow {n m k : ℕ} {d : Fin n → ℕ} {e : Fin m → ℕ}
    (hd : ∀ i, d i ≤ k) (he : ∀ i, e i ≤ k)
    {K : Set (Points n)} {S : Set (Points m)} (hK : IsCompact K) (hx : K ⊆ conf n)
    (hS : IsCompact S) (hy : S ⊆ Outside m) (p : ℕ) (B : ℝ) (hB : 0 < B) :
    RoundedAt (issuedDatum g hg) (Physical.Y0 (selectedVision.{u} g hg dates strictDates).pupil.last (filedFrame.{u} g hg dates strictDates) d e) (upper g.core 1 B) K S ((selectedVision.{u} g hg dates strictDates).T (issuedDatum g hg)) p := by
  classical
  obtain ⟨T₀, hT, clear, pay⟩ := ((eventually_ge_atTop (1 : ℝ)).and
    ((GradedFar259.always_clear hK hx hS hy).and
      (basisRows.{u} g hg dates strictDates hd he hK hx hS hy))).exists
  choose C hC j hj using (pay 1 B one_pos hB p)
  let a := Finset.univ.sup (fun bc : BasisSlots g.core d × BasisSlots g.core e => j bc.1 bc.2)
  have ja (b c) : j b c ≤ a :=
    Finset.le_sup (f := fun bc : BasisSlots g.core d × BasisSlots g.core e => j bc.1 bc.2)
      (Finset.mem_univ (b,c))
  have allRows := Filter.eventually_all.mpr fun b => Filter.eventually_all.mpr fun c => hj b c
  intro L R
  let L₀ := max L 0
  let R₀ := max R 0
  let D := ∑ b : BasisSlots g.core d, ∑ c : BasisSlots g.core e, L₀^n * (R₀^m * C b c)
  have Lpos : 0 ≤ L₀ := le_max_right .. 
  have Rpos : 0 ≤ R₀ := le_max_right ..
  have Dpos : 0 ≤ D := Finset.sum_nonneg fun b _ =>
    Finset.sum_nonneg fun c _ => mul_nonneg (pow_nonneg Lpos _) (mul_nonneg (pow_nonneg Rpos _) (hC b c))
  refine ⟨D+1, by linarith, a, (windows_eventually _ _).2 ⟨log T₀, ?_⟩⟩
  filter_upwards [allRows, g0_pos (_root_.IssuedMaxwell.ElectedPrescription.simple g hg), self_mem_nhdsWithin (s := Ioi (0:ℝ))] with r hrows hr radius
  intro s hs inWindow o x xK y yS u hu v hv
  let w : Window := (r,s)
  let T := exp s
  have hT' : T₀ ≤ T := calc
    T₀ = exp (log T₀) := (exp_log (zero_lt_one.trans_le hT)).symm
    _ ≤ exp s := exp_le_exp.mpr hs
  have s0 : 0 ≤ s := (log_nonneg hT).trans hs
  have hc : forest x (T • y) ∈ conf (n+m) := clear T hT' x xK y yS
  have hsqueezed : forest x (squeeze (-w.sep) y) ∈ conf (n+m) := by
    rw [Physical.Round.wide_here]; exact hc
  let f : Response g.core d e :=
    GradedFar259.Original.measures (selectedVision.{u} g hg dates strictDates).pupil.last ((selectedVision.{u} g hg dates strictDates).Post (issuedDatum g hg)) d e o r T x y -
      GradedFar259.Comparing.reading (Measure.outlook (issuedDatum g hg).scheme (issuedDatum g hg).criterion) hd he x (T • y) p ((selectedVision.{u} g hg dates strictDates).T (issuedDatum g hg) r)
  let rate := (g0 g.core r)^(p+1)*(1+s)^a
  have basis (b c) : ‖f (word b) (word c)‖ ≤ C b c * rate := by
    have q := hrows b c T hT' inWindow x xK y yS o
    rw [show log T = s from log_exp s] at q
    refine q.trans ?_
    change C b c * _ * (1+s)^(j b c) ≤ C b c * (_ * (1+s)^a)
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (le_add_of_nonneg_right s0) (ja b c))
      (mul_nonneg (hC b c) (pow_nonneg hr.le _))
  have hu' : u ∈ Balls L₀ g.core d := fun i c => (hu i c).trans (le_max_left ..)
  have hv' : v ∈ Balls R₀ g.core e := fun i c => (hv i c).trans (le_max_left ..)
  have bound := AppointedFlashBalls.response f u v Lpos Rpos hu' hv' C rate basis
  have sameY : Physical.Y0 (selectedVision.{u} g hg dates strictDates).pupil.last (filedFrame.{u} g hg dates strictDates) d e w o x y u v =
      GradedFar259.Original.measures (selectedVision.{u} g hg dates strictDates).pupil.last ((selectedVision.{u} g hg dates strictDates).Post (issuedDatum g hg)) d e o r T x y u v := by
    rw [Physical.Y0_value, GradedFar259.Original.measure_eq]; rfl
  have sameCrop : crop p ((selectedVision.{u} g hg dates strictDates).T (issuedDatum g hg) r) (Continuation.row (issuedDatum g hg) x u y v w.sep) =
      GradedFar259.Comparing.reading (Measure.outlook (issuedDatum g hg).scheme (issuedDatum g hg).criterion) hd he x (T • y) p ((selectedVision.{u} g hg dates strictDates).T (issuedDatum g hg) r) u v := by
    rw [Physical.Round.regimen (issuedDatum g hg) (electedPerspective.{u} g hg).MS (electedPerspective.{u} g hg).matching hsqueezed u v hd he,
      GradedFar259.Flash.readyPT (u := r) hc radius hd he u v]
    have points : Physical.Round.along w x y = GradedFar259.Flash.joins x y T := rfl
    have leftLabels : installedInputs hd u = GradedFar259.liftSlots hd u := by
      funext i
      rfl
    have rightLabels : installedInputs he v = GradedFar259.liftSlots he v := by
      funext i
      rfl
    rw [points, leftLabels, rightLabels, GradedFar259.crop_apply, YM.FVA2.GradedFar.crop_eq]
  change ‖Physical.Y0 (selectedVision.{u} g hg dates strictDates).pupil.last (filedFrame.{u} g hg dates strictDates) d e w o x y u v - crop p ((selectedVision.{u} g hg dates strictDates).T (issuedDatum g hg) r) (Continuation.row (issuedDatum g hg) x u y v w.sep)‖ ≤ _
  rw [sameY, sameCrop]
  change ‖f u v‖ ≤ (D+1)*(g0 g.core r)^(p+1)*(1+s)^a
  rw [mul_assoc]
  exact bound.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
    (mul_nonneg (pow_nonneg hr.le _) (pow_nonneg (add_nonneg zero_le_one s0) _)))

end YM.FVA2.GradedFar.AppointedFlashNumerator
