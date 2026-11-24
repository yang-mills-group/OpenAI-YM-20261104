import YM.Integration.WilsonGraphCenteredFarClockTransport
import YM.Integration.WilsonGraphCenteredFarEnteredRows
import YM.GradedFar.Physical.Fare

set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar.AppointedCenteredWindowReadings

open Filter Real PowerSeries Growth Continuation
open Register MS MS.Book MS.Land Scale
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Enh O.Score O.Canon Dframe Jury
open MS.Native MS.Menus MS.Tide MS.Book.Program
open YangMills YangMills.Matching YM.Answer.ContinuumLimit YM.Integration
open WilsonGraphCenteredFarReplacement (atFar)
open scoped Topology BigOperators Classical

universe u

private theorem atFarRadius {G : Gauge} (simple : G.Simple) {C B : ℝ}
    (hC : 0 < C) (hB : 0 < B) {P : ℝ → Prop}
    (paid : ∀ᶠ f : ℝ in 𝓝[>] 0, P f) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ s ≥ 0, exp s ≤ C * (gYM G r)^(-B) → P (r * exp s) := by
  have tail : ∀ᶠ w in Window.windows (upper G C B), P (Window.Coarse w) :=
    (Physical.coarse_motion simple hC hB).eventually paid
  obtain ⟨s₀,large⟩ := (Window.windows_eventually (upper G C B) (fun w => P (Window.Coarse w))).mp tail
  obtain ⟨ε,hε,small⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp paid)
  have near : ∀ᶠ r : ℝ in 𝓝[>] 0, r < ε / exp s₀ :=
    (gt_mem_nhds (div_pos hε (exp_pos _))).filter_mono nhdsWithin_le_nhds
  filter_upwards [large,near,self_mem_nhdsWithin] with r hr hshort hpositive
  intro s hs admitted
  by_cases long : s₀ ≤ s
  · exact hr s long admitted
  · have positive : 0 < r := hpositive
    have farPositive := mul_pos positive (exp_pos s)
    apply small
    · rw [Real.dist_eq,sub_zero,abs_of_pos farPositive]
      exact (mul_lt_mul_of_pos_left (exp_lt_exp.mpr (lt_of_not_ge long)) positive).trans
        ((lt_div_iff₀ (exp_pos _)).mp hshort)
    · exact farPositive

variable (g : GaugeGroup) (hg : g.IsSimple) (periods : ℕ → ℕ) (strict : StrictMono periods)
private abbrev scheme := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
private abbrev perspective := WilsonGraphPaperPublication.perspective.{u} g hg
private abbrev pick := WilsonGraphPaperPublication.publicPick.{u} g hg
  (ElectedPublication.order periods strict)
private abbrev hierarchy := YangMills.hierarchy (g := g) (pick.{u} g hg periods strict).pupil.last
  (pick.{u} g hg periods strict).pupil.P
private abbrev heater := (pick.{u} g hg periods strict).T (scheme g hg)

/-- The compact pair and its centered replacement are read at the same far radius and
heater throughout the filed distance window. The event precedes both labels and the viewer. -/
theorem onBothRulers (h q m : ℕ) (K : Set (YangMills.Points 2)) (compact : IsCompact K)
    (separated : K ⊆ YM.conf 2) {C B : ℝ} (hC : 0 < C) (hB : 0 < B) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ k : ℕ in atTop, ∃ D : ℝ, 0 ≤ D ∧
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ s ≥ 0, exp s ≤ C * (gYM g.core r)^(-B) →
      let f := r * exp s
      (∀ (a b : Sec g.core h) (phase : Option (hierarchy.{u} g hg periods strict).Character)
        (o y : Spacetime),
        let x : YangMills.Points 2 := WithLp.toLp 2 ![0,y]
        x ∈ K →
          AppointedCenteredRows.FiledPair.{u} g hg periods strict h q A r r f a b
            (atFar.{u} g hg periods strict h r f a) (atFar.{u} g hg periods strict h r f b) phase o y ∧
          AppointedCenteredRows.FiledPair.{u} g hg periods strict h q A r f f a b
            (atFar.{u} g hg periods strict h r f a) b phase o y) ∧
      let L := chairs g.core h (AppointedCenteredReverse.transfer.{u} g hg periods strict h r f)
      let U := chairs g.core h (atColumn (Kseries (scheme g hg) (perspective.{u} g hg).MS h s) k
        (heater.{u} g hg periods strict f))
      ‖L - U‖ ≤ D * (gYM g.core r)^(m+1) := by
  obtain ⟨A,hA,late⟩ := AppointedCenteredRows.enteredOnPick.{u} g hg periods strict h q K compact separated
  have physical := atFarRadius (_root_.IssuedMaxwell.ElectedPrescription.simple g hg) hC hB late
  refine ⟨A,hA,?_⟩
  filter_upwards [AppointedCenteredTransport.atFarClock.{u} g hg periods strict h m hC hB] with k earned
  obtain ⟨D,hD,close⟩ := earned
  refine ⟨D,hD,?_⟩
  filter_upwards [physical,close] with r rows columns
  intro s hs admitted
  exact ⟨rows s hs admitted r,columns s hs admitted⟩

end YM.FVA2.GradedFar.AppointedCenteredWindowReadings
