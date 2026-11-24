import YM.Integration.FVA1Physical.Exchange.ContinuumLimitOriginalForestMask

/-! The exact positive density and normalized mixed mark on the original
gauge-fixed Haar slice. The entire slice has the actual receiving vacuum
as its mass, so local comparison may price the complement on this law. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.OriginalMixedWilson
open Finset Filter Function MeasureTheory RG Wilson Gauge Precision Tree Lattice Exterior
open Next.SectorChange Comparison.RG02 Order Marker Multi
open Integral Actual Push.SectorMeasure
open scoped Topology BigOperators Classical
variable {G : Gauge} {I : Type} [DecidableEq I] {R : Census I}
variable (H:History G) (hs:H.Selected) {N n j:ℕ} (step:j<N)
local notation "S" => H.levels.clock.op j n
local notation "Fine" => Config G (H.S.side (j+1) n)
local notation "Coarse" => Config G (H.S.side j n)
local notation "fine" => H.rep N n (j+1)
local notation "coarse" => H.rep N n j

def forestWeight (F : Forest (S).ratio) (V:Coarse) (y:F.Slice G) : ℝ :=
  (S).density (H.β N n (j+1)) (F.drape y) V * (fine).eval (F.drape y)

include hs step
theorem forest_weight_nonnegative (F : Forest (S).ratio) (V:Coarse) (y:F.Slice G) :
    0 ≤ forestWeight H (N:=N) F V y :=
  mul_nonneg ((S).density_positive ..) (H.nonnegative hs N n (j+1) step _)

theorem forest_measured_column (F : Forest (S).ratio) (V:Coarse) (D:Lit R Fine)
    (quiet : ∀u,(D u).part R.quiet=((fine).eval u:ℂ)) (ok:Leaf.All D) :
    let k := forestWeight H (N:=N) F V
    let m := fun y:F.Slice G => unitScale (D (F.drape y))
    Integrable k (F.order G) ∧ ∀s:R.Mode,
      Integrable (fun y=>(k y:ℂ)*(m y).part s) (F.order G) ∧
      ∀(A:Set (F.Slice G)),MeasurableSet A →
      (forestRead F (fine).beta V D A).part s = ∫y in A,(k y:ℂ)*(m y).part s ∂F.order G := by
  intro k m
  let X := fun y:F.Slice G=>((S).density (fine).beta (F.drape y) V:ℂ) • D (F.drape y)
  have good : Good (F.order G) X := by
    have eq : X=∑ t:(S).Choices, Actual.stack t V (fine).beta D ∘ F.drape := by
      funext y
      simpa only [X,Finset.sum_apply,Function.comp_apply] using congrFun
        (@Actual.collective G _ _ S I _ R V (fine).beta D) (F.drape y)
    rw [eq]
    exact Good.sum univ (fun t _=>good_slice F t V (fine).beta (H.levels.blocks j n).branches ok)
  have money (y:F.Slice G) : (X y).part R.quiet = (k y:ℂ) := by
    change (((S).density (fine).beta (F.drape y) V:ℂ) • D (F.drape y)).part R.quiet=_
    rw [Poly.part_smul,quiet,←Complex.ofReal_mul]
    rfl
  have entry (s:R.Mode) (y:F.Slice G) : (X y).part s = (k y:ℂ)*(m y).part s := by
    have nz := Complex.ofReal_ne_zero.mpr
      (SectorNext.Vacuum.strictly H hs N n (j+1) step (F.drape y)).ne'
    change (((S).density (fine).beta (F.drape y) V:ℂ) • D (F.drape y)).part s =
      ((forestWeight H (N:=N) F V y):ℂ)*(unitScale (D (F.drape y))).part s
    rw [Poly.part_smul,forestWeight,Complex.ofReal_mul,unitScale,Poly.part_smul,quiet]
    field_simp
  constructor
  · apply (good R.quiet).re.congr
    exact Eventually.of_forall (fun y=>by change ((X y).part R.quiet).re=k y; rw [money];rfl)
  intro s
  refine ⟨(good s).congr (Eventually.of_forall (entry s)),?_⟩
  intro A hm
  unfold forestRead
  rw [components,mark_cut,integral_indicator hm]
  exact integral_congr_ae (Eventually.of_forall (entry s))

theorem forest_original_volume (F : Forest (S).ratio) (V:Coarse) (D:Lit R Fine)
    (quiet : ∀u,(D u).part R.quiet=((fine).eval u:ℂ)) (ok:Leaf.All D)
    (invariant:GaugeInvariant D) :
    (∫y,forestWeight H (N:=N) F V y ∂F.order G)=(coarse).eval V := by
  let k := forestWeight H (N:=N) F V
  have all := forest_measured_column H hs step F V D quiet ok
  have cash := (all.2 R.quiet).2 Set.univ MeasurableSet.univ
  rw [forest_read_full F (fine).beta V (H.levels.blocks j n).branches D ok invariant,
    (measured_quiet H hs step D quiet V).1,Measure.restrict_univ] at cash
  have one (y:F.Slice G) : (unitScale (D (F.drape y))).part R.quiet=1 :=
    unitScore ((quiet (F.drape y)) ▸ Complex.ofReal_ne_zero.mpr
      (SectorNext.Vacuum.strictly H hs N n (j+1) step (F.drape y)).ne')
  dsimp only at cash
  simp_rw [one,mul_one] at cash
  rw [integral_complex_ofReal] at cash
  exact Complex.ofReal_inj.mp cash.symm
end YM.Integration.FVA1Physical.OriginalMixedWilson
