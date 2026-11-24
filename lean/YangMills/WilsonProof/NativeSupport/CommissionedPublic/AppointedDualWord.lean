import YangMills.WilsonProof.NativeSupport.CommissionedPublic.AppointedPaperOrdinary

set_option autoImplicit false
set_option maxHeartbeats 2400000

noncomputable section
namespace YM.Integration.GradedFar.AppointedDualWord
open Function Filter Set PowerSeries MeasureTheory Metric
open Wilson RG Source Extraction Table Spec PhysicalNext.Repeat.Legato RG17 FullVolume
open Climb Trace.Pilot PhysMS OPE OPE.Orbits
open XSpace XSpace.Normalize FVA2 FVA2.Register FVA2.Scale
open MS MS.Native MS.Land MS.Fleet
open Dframe O O.Score O.Enh FVA2.GradedFar
open Batch Auth Tariff Tariff.Playbill Tariff.Sunshine
open Answer.ContinuumLimit Answer.ContinuumLimit.Vision
open scoped Topology BigOperators Classical ContDiff

universe u
variable (g : YangMills.GaugeGroup) (hg : g.IsSimple)
variable (periods : ℕ → ℕ) (mono : StrictMono periods)


/-- Each physical input and test use the same grade-h Daylight basis. -/
theorem word {G : Gauge} {n h : ℕ} {X : Set (Points n)} (openX : IsOpen X)
    {x : Points n} (inside : x ∈ X) (L : TraceOrder n)
    (out : Module.Dual ℂ (Sec G h)) (f : Points n → Sec G h)
    (smooth : ∀ a : Toon G h, ContDiffOn ℝ ∞ (fun y => coord a (f y)) X) :
    δ L (fun y => out (f y)) x =
      ∑ a : Toon G h, out (theory a) * δ L (fun y => coord a (f y)) x := by
  have same : EqOn (fun y => out (f y))
      (fun y => ∑ a : Toon G h, out (theory a) * coord a (f y)) X := by
    intro y _
    change out (f y) = ∑ a : Toon G h, out (theory a) * coord a (f y)
    rw [AppointedPaperOrdinary.wholeDual out (f y)]
    apply Finset.sum_congr rfl
    intro a _
    exact mul_comm _ _
  rw [δ_congr openX same L inside]
  rw [δ_sum openX Finset.univ (fun a y => out (theory a) * coord a (f y))
    (fun a _ => contDiffOn_const.mul (smooth a)) L inside]
  apply Finset.sum_congr rfl
  intro a _
  exact δ_const_mul openX (smooth a) (out (theory a)) L inside

theorem priceWord {G : Gauge} {n h : ℕ} {X : Set (Points n)} (openX : IsOpen X)
    {x : Points n} (inside : x ∈ X) (L : TraceOrder n) (out : Module.Dual ℂ (Sec G h))
    (f g : Points n → Sec G h)
    (smoothF : ∀ a : Toon G h, ContDiffOn ℝ ∞ (fun y => coord a (f y)) X)
    (smoothG : ∀ a : Toon G h, ContDiffOn ℝ ∞ (fun y => coord a (g y)) X)
    (D : Toon G h → ℝ) (err : ℝ)
    (paid : ∀ a, ‖δ L (fun y => coord a (f y)) x - δ L (fun y => coord a (g y)) x‖
      ≤ D a * err) :
    ‖δ L (fun y => out (f y)) x - δ L (fun y => out (g y)) x‖ ≤
      (∑ a : Toon G h, ‖out (theory a)‖ * D a) * err := by
  rw [word openX inside L out f smoothF, word openX inside L out g smoothG,
    ← Finset.sum_sub_distrib, Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro a _
  rw [← mul_sub, norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (paid a) (norm_nonneg _)
private abbrev submitted {n : ℕ} (d : Fin n → ℕ) (v : AppointedH140Inputs g.core d) :
    Fin n → Σ e : ℕ, (YangMills.maxwellReference g).sector e :=
  fun i => ⟨d i, v i⟩


private abbrev actualField {n h : ℕ} {d : Fin n → ℕ} (r : ℝ) (o : E4)
    (v : AppointedH140Inputs g.core d) (x : Points n) : Sec g.core h :=
  (_root_.YM.Answer.ContinuumLimit.AppointedOrdinaryPacket.measurement hg (_root_.YM.Integration.WilsonGraphPaperPublication.publicPick.{u} g hg (_root_.YM.Answer.ContinuumLimit.ElectedPublication.order periods mono)) (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (_root_.YM.Integration.WilsonGraphPaperPublication.perspective.{u} g hg)).wilsonOPE
    r h (submitted g d v) o x
private abbrev actualCrop {n h : ℕ} {d : Fin n → ℕ} (q : ℕ) (ν r : ℝ)
    (v : AppointedH140Inputs g.core d) (x : Points n) : Sec g.core h :=
  msVector (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (_root_.YM.Integration.WilsonCapturedPhysicalMSDatum.original g.core)
    ν v x q h ((_root_.YM.Integration.WilsonGraphPaperPublication.publicPick.{u} g hg (_root_.YM.Answer.ContinuumLimit.ElectedPublication.order periods mono)).T (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) r)

theorem onPaper {n ℓ h : ℕ} {d : Fin n → ℕ} {K : Set (Points n)}
    (compact : IsCompact K) (sep : K ⊆ conf n)
    (prior : M2Continuation.Prior (_root_.YM.Integration.WilsonGraphPaperPublication.publicPick.{u} g hg (_root_.YM.Answer.ContinuumLimit.ElectedPublication.order periods mono)).pupil.last (_root_.YM.Integration.WilsonGraphPaperPublication.publicPick.{u} g hg (_root_.YM.Answer.ContinuumLimit.ElectedPublication.order periods mono)).pupil.J (_root_.IssuedMaxwell.ElectedPrescription.issued g hg))
    (traced : LogTrace (_root_.YM.Integration.WilsonGraphPaperPublication.publicPick.{u} g hg (_root_.YM.Answer.ContinuumLimit.ElectedPublication.order periods mono)).pupil.last (_root_.YM.Integration.WilsonGraphPaperPublication.publicPick.{u} g hg (_root_.YM.Answer.ContinuumLimit.ElectedPublication.order periods mono)).pupil.P.port)
    (hd : AppointedH140Through ℓ d) (hh : h ≤ ℓ) (q : ℕ) (ν : ℝ)
    (out : Module.Dual ℂ (Sec g.core h)) (L : TraceOrder n)
    (smooth : ∀ᶠ r in trail, ∀ o x, x ∈ K → ∀ v : AppointedH140Inputs g.core d, Box v 1 →
      ∃ X : Set (Points n), IsOpen X ∧ x ∈ X ∧
        (∀ a : Toon g.core h, ContDiffOn ℝ ∞
          (fun y => coord a (actualField.{u} g hg periods mono r o v y)) X) ∧
        (∀ a : Toon g.core h, ContDiffOn ℝ ∞
          (fun y => coord a (actualCrop.{u} g hg periods mono q ν r v y)) X)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ r in trail, ∀ o x, x ∈ K → ∀ v : AppointedH140Inputs g.core d, Box v 1 →
      ‖δ L (fun y => out (actualField.{u} g hg periods mono r o v y)) x -
        δ L (fun y => out (actualCrop.{u} g hg periods mono q ν r v y)) x‖ ≤
          A * ((_root_.YM.Integration.WilsonGraphPaperPublication.publicPick.{u} g hg (_root_.YM.Answer.ContinuumLimit.ElectedPublication.order periods mono)).T (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) r) ^ (q + 1) := by
  have H := (AppointedPaperOrdinary.allWords.{u} g hg periods mono compact sep prior traced hd hh q ν).2 L
  choose D hD pay using H
  refine ⟨∑ a : Toon g.core h, ‖out (theory a)‖ * D a,
    Finset.sum_nonneg (fun a _ => mul_nonneg (norm_nonneg _) (hD a)), ?_⟩
  have common := Filter.eventually_all.2 pay
  filter_upwards [smooth, common] with r hr hs
  intro o x hx v hv
  obtain ⟨X,hX,inside,hf,hg'⟩ := hr o x hx v hv
  exact priceWord hX inside L out _ _ hf hg' D _ (fun a => hs a o x hx v hv)

end YM.Integration.GradedFar.AppointedDualWord
end

