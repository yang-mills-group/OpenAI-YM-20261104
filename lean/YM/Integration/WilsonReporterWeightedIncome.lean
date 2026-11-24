import YM.TraceExtension.Prom.Sway.Tilt
import YM.MergeProof.North.Sultan

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReporterWeightedIncome
open Next.Rank Next.Rank.Ribbon MergeProof
open Function Filter RG Thirst Baler Lattice Wilson MeasureTheory Marker Perch Station Cells Spindle Atlas
open MergeProof.Ribbons MergeProof.Float PhysicalNext.Repeat.Legato.Bandage
open scoped BigOperators Classical Topology

variable {G : Gauge} (C : Family G) {W : Bid.Worth} {u ψ φ δ : ℕ → ℝ} {r : ℕ → ℕ}
    {door : ∀ N p m : ℕ, m < N → GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}

theorem solves {d k N p : ℕ} {b : ℝ} {M : Module.End ℂ (C.label d)} {t g : C.label d}
    (h : Price.Solves C b d k N p M g t) (z : ℂ) :
    Price.Solves C b d k N p M (z • g) (z • t) := by
  unfold Price.Solves at h ⊢
  simpa only [map_smul] using congrArg (z • ·) h

/-- The enlargement is paid by the actual field's attained finite stamp.
The stamp need only bound its chosen polynomial on the enlarged dose. -/
theorem original (h : G.Simple) (H : C.Makes) (hp : Scrim C W u ψ φ δ (fly C.path.levels) r door)
    (d D : ℕ) (g : C.label d) : ∀ᶠ k : ℕ in atTop,
    ∀ b e add : ℝ, 0 ≤ b → e+add+(b*d+saves C d) ≤ -8 →
    year C D k → ∀ N p : ℕ, k≤N → ∀ {Q q X} (T : StampDuty C k N p d D Q q X) t,
    Price.Solves C (mag C.path.levels b k) d k N p T.T g t →
    let s := clim C.path.levels k
    let a : ℂ := (Perch.bill add s : ℝ)
    let row := a • t
    Price.Solves C (mag C.path.levels b k) d k N p T.T (a • g) row ∧
      Perch.bill e s * moneys C d k N p row ≤ Perch.bill (-8) s ∧
      Rise.coin (T.W row) ≤ Perch.bill (add+(b*d+saves C d)) s := by
  filter_upwards [Atlas.incomeSky h H g,eventually_ge_atTop (C.ref d)] with k inc refK
  intro b e add hb budget stage N p top Q q X T t fit s a row
  have inc' := inc b hb N p top T.T T.lights.span t fit
  rw [fire_bill] at inc'
  let E := b*d+saves C d
  have inc₀ : Perch.bill 1 s * paid C d k N p t ≤ Perch.bill E s := inc'
  have a_pos : 0 < Perch.bill add s := Real.exp_pos _
  have bound : paid C d k N p row = Perch.bill add s * paid C d k N p t := by
    change paid C d k N p (a • t)=_
    rw [MergeProof.Ribbons.paid_scale C N p k d H hp refK t a top]
    simp only [a,Complex.norm_real,Real.norm_of_nonneg a_pos.le]
  have total : Perch.bill 1 s * paid C d k N p row ≤ Perch.bill (add+E) s := by
    rw [bound]
    calc
      _ = Perch.bill add s * (Perch.bill 1 s * paid C d k N p t) := by ring
      _ ≤ _ := (mul_le_mul_of_nonneg_left inc₀ a_pos.le).trans_eq (Perch.overlap ..)
  have col : (C.path.levels.params k).columns ≤ Perch.bill 1 s := stage.trans
    (Glimmer.billed _ (show LiftMark.shade D/4≤1 by linarith only [LiftMark.shaded D]))
  have earnings : moneys C d k N p row ≤ Perch.bill (add+E) s :=
    (mul_le_mul_of_nonneg_right col (paid_pos ..)).trans total
  refine ⟨solves C fit a,?_,(T.weight _).trans total⟩
  apply (mul_le_mul_of_nonneg_left earnings (Real.exp_pos _).le).trans
  change Perch.bill e s * Perch.bill (add+E) s ≤ _
  rw [Perch.overlap]
  exact Glimmer.billed _ (by dsimp only [E]; linarith only [budget])

end YM.Integration.WilsonReporterWeightedIncome
