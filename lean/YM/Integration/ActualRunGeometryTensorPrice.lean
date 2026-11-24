import YM.Integration.ActualInputGeometryCoordinates
import YM.Integration.ActualStationaryTensorPrice
import YM.Integration.ActualRunLoopTensorPrice
import YM.Integration.ActualInputLayerTensorPrice
import YM.Integration.NativeJointPayloadAnalytic
import YM.Integration.ActualKernelHaarPort
import YM.Integration.SeparatedComponentMarginal
import YM.Integration.FiniteOptionSlotMarginal

/-! Full restored-layer geometric vertices on the original Run.
All coupling/field slot patterns are retained. Constants and the level event
precede cutoff, period, kernel, original layer record and tensor coordinates.
This prices the auxiliary geometry; the supplied input is attached by its
separately proved finite tensor identity, not by a global vacuum replacement. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualRunGeometryTensorPrice
open Function Filter Set Metric Lattice Wilson RG Precision Tree Exterior
open IterationFour IterationFour.Vacuum LocalComparison LocalComparison.Global FullQLocal
open FullQLocal.RenderedStep Push.Uniform Comparison.RG02
open PhysicalNext.Repeat.Legato
open scoped Topology BigOperators Classical ContDiff

private theorem loop_cap_le {G : Gauge} {V : Type} {T : Run G} {J : Request V}
    (A : NumericSchedule T.family J) (i : ℕ) :
    T.family.path.levels.clock.loopCap (i + 1) ≤ A.admittedCost i := by
  let a := T.family.path.levels
  have hl (j : ℕ) : 0 ≤ a.clock.loopCap j := by
    change 0 ≤ 2 * (a.clock.monitor j) ^ (a.clock.theta (a.clock.J j))
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg (Real.exp_nonneg _) _)
  have hm (j : ℕ) : 0 ≤ a.clock.monitor j := Real.exp_nonneg _
  have hc0 : 0 ≤ (a.clock.coverSize i : ℝ) := Nat.cast_nonneg _
  have hc1 : 0 ≤ (a.clock.coverSize (i + 1) : ℝ) := Nat.cast_nonneg _
  have hp0 := (a.params i).paths_pos
  have hp1 := (a.params (i + 1)).paths_pos
  have hk0 := (a.params i).columns_ge
  have hk1 := (a.params (i + 1)).columns_ge
  have hr0 := (a.params i).clip.radius_pos
  have hr1 := (a.params (i + 1)).clip.radius_pos
  have hb := A.cost_covers_geometry i
  change 1 + (a.clock.coverSize i : ℝ) + (a.clock.coverSize (i + 1) : ℝ) +
    a.clock.monitor i + a.clock.monitor (i + 1) + a.clock.loopCap i +
    a.clock.loopCap (i + 1) + (a.params i).paths + (a.params (i + 1)).paths +
    (a.params i).columns + (a.params (i + 1)).columns +
    (a.params i).clip.relaxation + (a.params (i + 1)).clip.relaxation ≤
      A.admittedCost i at hb
  linarith [hl i, hm i, hm (i + 1)]

private theorem one_side {G : Gauge} {V : Type} {T : Run G} {J : Request V}
    (A : NumericSchedule T.family J) {C : ℝ} (hC : 0 ≤ C) (e i : ℕ)
    (h : C * Real.log (T.family.path.levels.clock.hatBeta i) ^ e +
      C * Real.log (T.family.path.levels.clock.hatBeta (i + 1)) ^ e ≤ A.admittedCost i) :
    C * Real.log (T.family.path.levels.clock.hatBeta i) ^ e ≤ A.admittedCost i := by
  have hn := mul_nonneg hC
    (pow_nonneg (Real.log_pos (T.family.path.levels.fits.delayed (i + 1))).le e)
  linarith

/-- Every remaining Option-coordinate is summed, with one genuine field anchor.
The original full Surface, loop, Haar and all nonlinear payloads are included. -/
theorem geometry_marginal {G : Gauge} (T : Run G) (hG : G.Simple)
    (hT : ActualRunNativeComponentRecipe.Attached T)
    {V : Type} {J : Request V} (A : NumericSchedule T.family J)
    (n cap : ℕ) (hn : 2 ≤ n) :
    let a := T.family.path.levels
    ∃ C : ℝ, 0 < C ∧ ∃ e : ℕ,
      ∀ᶠ i : ℕ in atTop, ∀ N period : ℕ, i + 1 ≤ N →
        let S := a.clock.op i period
        let Q := T.family.path.rep N period (i + 1)
        ∀ (O : ChartRatio G) (K : Bulk.Kernel S Q.clip Q.path O)
          (p : BudgetPoint) (order : ℕ)
          (layers : List (Piece G (T.family.side (i + 1) period)))
          (_H : GradedVacuumLayers layers p order cap (A.inputWidth i) (A.admittedCost i))
          (B : Forest S.ratio) (t : S.Choices),
        ∀ k : ℕ, k + 1 ≤ n → ∀ j : Fin (k + 1), ∀ i0 : Push.Uniform.Joint B G,
          (∑ q : Fin k → Option (Push.Uniform.Joint B G),
            ‖(((k + 1).factorial : ℝ)⁻¹) *
              iteratedFDeriv ℝ (k + 1)
                (ActualInputGeometryCoordinates.arrayGeometry K B t layers) 0
                (fun u => FiniteOptionSlotMarginal.direction
                  (fun z : Push.Uniform.Joint B G => bolt z)
                  (Fin.insertNth (α := fun _ => Option (Push.Uniform.Joint B G)) j (some i0) q u))‖) ≤
            C * (A.admittedCost i) ^ e := by
  dsimp only
  let a := T.family.path.levels
  obtain ⟨Cm, hCm, em, hm⟩ := ActualStationaryTensorPrice.surface_marginal T hT n hn
  obtain ⟨Cl, hCl, el, hl⟩ := ActualRunLoopTensorPrice.loop_marginal T hT n
  obtain ⟨Cr, hCr, er, hr⟩ := ActualInputLayerTensorPrice.layers_marginal T hG hT A n cap
  obtain ⟨Z, hpaint⟩ := paint_supply G n
  let Ch : ℝ := ∑ d ∈ Finset.range n, ActualKernelHaarPrice.onePortCost G d
  have hCh : 0 ≤ Ch := Finset.sum_nonneg fun d _ => by
    unfold ActualKernelHaarPrice.onePortCost
    positivity
  let e := max 2 er
  let C := 2 + Ch + Cr
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨(2 : ℝ) ^ n * C, by positivity, e, ?_⟩
  filter_upwards [hm, hl, hr, A.logarithmic_cost hG Cm em,
    A.logarithmic_cost hG Cl el] with i hmi hli hri hpmi hpli
  intro N period hN O K p order layers H B t k hk j i0
  let W := A.admittedCost i
  have hW1 : 1 ≤ W := A.admitted_cost_ge_one i
  have hW : 0 ≤ W := A.admitted_cost_nonnegative i
  have hconv : T.family.path.Conv N period (i + 1) :=
    T.makes.wilson.represents N period (i + 1) hN
  have hmain := hmi N period hN B t
  rw [← hconv.clip] at hmain
  have hloop := hli N period hN B
  have hmainCost : Cm * Real.log (a.clock.hatBeta i) ^ em ≤ W :=
    one_side A hCm.le em i hpmi
  have hloopCost : Cl * Real.log (a.clock.hatBeta i) ^ el ≤ W :=
    one_side A hCl.le el i hpli
  have hcap : a.clock.loopCap (i + 1) ≤ W := loop_cap_le A i
  let main := priced B t (T.family.path.rep N period (i + 1)).clip
    (T.family.path.rep N period (i + 1)).path
  have hsurface : Bulk.Surface (a.clock.op i period)
      (T.family.path.rep N period (i + 1)).clip
      (T.family.path.rep N period (i + 1)).path B t ∘ paint B G = main := rfl
  rw [hsurface] at hmain
  let light := fun z => loop (T.family.path.rep N period (i + 1)).path (fine G B z)
  let heavy := fun z : Positions (Push.Uniform.Joint B G) =>
    Real.log (∏ b : B.Free, O.J ((paint B G z).2 b))
  let field := fun row : Piece G (T.family.side (i + 1) period) =>
    fun z => unmaskedPayload row.packet (fine G B z)
  have hgeometry : SeparatedComponentMarginal.separated main light heavy layers
      (fun row => row.power + 2 - row.rank) field =
      ActualInputGeometryCoordinates.arrayGeometry K B t layers := rfl
  have hfield (row : Piece G (T.family.side (i + 1) period)) (hrow : row ∈ layers) :
      AnalyticAt ℝ (field row) 0 :=
    (NativeJointPayloadAnalytic.payload_analytic_zero B H hpaint
      (A.input_width_pos i) row hrow).analyticAt
  have hh : AnalyticAt ℝ heavy 0 := (ActualKernelHaarPort.kernel_log_contDiffAt K B).analyticAt
  have hpow : 1 ≤ W ^ e := one_le_pow₀ hW1
  have hlinear : W + W ^ 2 + Ch + Cr * W ^ er ≤ C * W ^ e := by
    have hw1 : W ≤ W ^ e := by
      simpa only [pow_one] using pow_le_pow_right₀ hW1 (show 1 ≤ e by dsimp [e]; omega)
    have hw2 : W ^ 2 ≤ W ^ e := pow_le_pow_right₀ hW1 (le_max_left _ _)
    have hwr : W ^ er ≤ W ^ e := pow_le_pow_right₀ hW1 (le_max_right _ _)
    have hhc : Ch ≤ Ch * W ^ e := le_mul_of_one_le_right hCh hpow
    have hrr := mul_le_mul_of_nonneg_left hwr hCr.le
    dsimp only [C]
    nlinarith
  have hbound := FiniteOptionSlotMarginal.anchored_direction_bound
    (fun u => ‖(((k + 1).factorial : ℝ)⁻¹) *
      iteratedFDeriv ℝ (k + 1)
        (ActualInputGeometryCoordinates.arrayGeometry K B t layers) 0 u‖)
    (fun z : Push.Uniform.Joint B G => bolt z) j i0 (C * W ^ e) (by
    intro c d he σ
    have hd : d + 1 ≤ n := by omega
    let cost := fun row : Piece G (T.family.side (i + 1) period) =>
      ∑ q : Fin d → Push.Uniform.Joint B G,
        ‖(((d + 1).factorial : ℝ)⁻¹) * iteratedFDeriv ℝ (d + 1)
          (field row) 0 (fun u => bolt (Fin.cons (α := fun _ => Push.Uniform.Joint B G) i0 q u))‖
    have hmainBound : (∑ q : Fin d → Push.Uniform.Joint B G,
        ‖(((d + 1).factorial : ℝ)⁻¹) * iteratedFDeriv ℝ (d + 1) main 0
          (fun u => bolt (Fin.cons (α := fun _ => Push.Uniform.Joint B G) i0 q u))‖) ≤ W := by
      simpa only [entry, smul_eq_mul, Fin.insertNth_zero'] using
        (hmain.2 d hd 0 i0).trans hmainCost
    have hloopBound : (∑ q : Fin d → Push.Uniform.Joint B G,
        ‖(((d + 1).factorial : ℝ)⁻¹) * iteratedFDeriv ℝ (d + 1) light 0
          (fun u => bolt (Fin.cons (α := fun _ => Push.Uniform.Joint B G) i0 q u))‖) ≤ W ^ 2 := by
      have hnon : 0 ≤ Cl * Real.log (a.clock.hatBeta i) ^ el :=
        mul_nonneg hCl.le (pow_nonneg (Real.log_pos (a.fits.delayed i)).le el)
      have hpaid : a.clock.loopCap (i + 1) *
          (Cl * Real.log (a.clock.hatBeta i) ^ el) ≤ W ^ 2 := by
        simpa only [pow_two] using mul_le_mul hcap hloopCost hnon hW
      simpa only [light, entry, smul_eq_mul, Fin.insertNth_zero'] using
        (hloop.2 d hd 0 i0).trans hpaid
    have hhaarBound : (∑ q : Fin d → Push.Uniform.Joint B G,
        ‖(((d + 1).factorial : ℝ)⁻¹) * iteratedFDeriv ℝ (d + 1) heavy 0
          (fun u => bolt (Fin.cons (α := fun _ => Push.Uniform.Joint B G) i0 q u))‖) ≤ Ch := by
      have hc : ActualKernelHaarPrice.onePortCost G d ≤ Ch :=
        Finset.single_le_sum (fun r _ => by unfold ActualKernelHaarPrice.onePortCost; positivity)
          (Finset.mem_range.mpr (by omega))
      simpa only [heavy, entry, smul_eq_mul, Fin.insertNth_zero'] using
        (ActualKernelHaarPort.kernel_normalized_port_l1 K B d 0 i0).trans hc
    have hrows : (layers.map cost).sum ≤ Cr * W ^ er := by
      simpa only [cost, field, entry, smul_eq_mul, Fin.insertNth_zero'] using
        hri period p order layers H B d hd 0 i0
    have hb := SeparatedComponentMarginal.marginal layers
      (fun row => row.power + 2 - row.rank) field main light heavy
      hmain.1.analyticAt hloop.1.analyticAt hh hfield c d
      (fun z : Push.Uniform.Joint B G => bolt z) 0 i0 σ W (W ^ 2) Ch cost
      hmainBound hloopBound hhaarBound (fun _ _ => le_rfl)
    have ht := hb.trans ((add_le_add (le_refl (W + W ^ 2 + Ch)) hrows).trans hlinear)
    have horder : c + d = k := Nat.succ.inj he
    subst k
    simp only [hgeometry, Fin.insertNth_zero', Function.comp_def] at ht
    refine le_trans (le_of_eq ?_) ht
    apply Finset.sum_congr
    · ext q
      simp
    · intro q _
      rfl
  )
  exact hbound.trans (by
      have hp : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ n :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      calc
        _ ≤ (2 : ℝ) ^ n * (C * W ^ e) :=
          mul_le_mul_of_nonneg_right hp (mul_nonneg hC.le (pow_nonneg hW e))
        _ = ((2 : ℝ) ^ n * C) * W ^ e := by ring)

end YM.Integration.ActualRunGeometryTensorPrice
end
