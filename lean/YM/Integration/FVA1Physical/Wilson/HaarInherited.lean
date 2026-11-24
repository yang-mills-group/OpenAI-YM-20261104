import YM.Integration.FVA1Physical.Wilson.HaarPatch
import YM.Integration.FVA1Physical.Wilson.InheritedPatch

/-! Quantitative mixed-source comparison over a positive, physically measured
Haar neighborhood at every incoming depth. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter MeasureTheory Set Finset Lattice RG YM.Wilson Tree Precision Exterior RGComparison.Core16
open FVA2.CityHistory PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested
open MSbar MSbar.Lis MSbar.Whisk MSbar.Rolling MSbar.Midpoint MSbar.Wave MSbar.Bakery MSbar.Cacao Comparison.RG02 Push Push.Uniform
open PhysicalNext.Repeat.Legato
open scoped Classical Topology ContDiff
variable {G : Gauge} {C : Family G} (L : Bulk.Chain C.path)
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem linear_tilt {ξ : ℝ} (hn : 0 ≤ ξ) (small : ξ ≤ 1) :
    Real.exp (2*ξ)-1 ≤ (2*Real.exp 2)*ξ := by
  let b := 2*ξ
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-b)) (Real.exp_pos b).le
  rw [←Real.exp_add,add_neg_cancel,Real.exp_zero] at h
  have k := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (show b ≤ 2 by dsimp [b];linarith))
    (show 0 ≤ b by dsimp [b];positivity)
  change Real.exp b-1 ≤ (2*Real.exp 2)*ξ
  dsimp [b] at *
  nlinarith only [h,k]

/-- One ultraviolet cutoff works for every period and field horizon in the selected
scene. Each admissible regular nonflat background has a positive true Haar cell.
All mixed tests, with arbitrary complex phases or Banach-valued readings, have the
linear error price on this cell. The size of its normalization need not be paid. -/
theorem inherited_haar_readings (u : G.ColorIndex) (simple : G.Simple) (sel : C.path.Selected)
    (D : Docket C u L.O L.horizon L.kin) (s p m : ℕ) (hs : 6 ≤ s) (hm : 4 ≤ m)
    (hp : p+3 ≤ m) {η : ℝ} (hη : 0<η) :
    ∀ᶠ k : ℕ in atTop, ∀ N n, k ≤ N → ∃ S : Scene C.path.levels n (p+1),
      Realized L.kin N n k (p+1) (Lis.sun G u) S ∧
      ∀ j, k ≤ j → ∀ hj : j<N, ∀ (T : Slices C.path.levels n) (h : (traversal T hj).Room G)
        (tag : (traversal T hj).Tags) (V : Config G (C.side j n))
        (x : Positions (Primary (C.side (j+1) n) G)) (H : ℝ), 0<H →
        let Q := C.path.rep N n (j+1)
        let g := Heath.Stock.cue Q.beta
        let w := Mosaic.vol (C.path.levels.clock.hatBeta (j+1))
        let d := H*(g^((p:ℝ)+1-η)/w)
        let U := haarPatch g w H x
        let σ := prior G (C.side (j+1) n)
        let μ := σ.restrict U
        let K := fun U=> (C.path.levels.clock.op j n).density Q.beta U V
        ‖x‖<w → (∀ e, ‖g • panel G _ x e‖ < (LocalH.geom_patch G).choose) →
        0<σ U ∧ (d ≤ 1 → ∀ (F : Config G (C.side (j+1) n) → E), AEStronglyMeasurable F μ →
          ∀ M : ℝ, 0 ≤ M → (∀ᵐ U ∂μ, ‖F U‖ ≤ M) →
          ‖patchMean μ (fun U=>K U * Q.eval U) F - patchMean μ
            (fun U=>K U * Real.exp (boundaryBank L S T hj h tag p g (chartLog g U))) F‖ ≤ (2*Real.exp 2)*d*M) := by
  have high := Multi.Wage.hat_tend simple C.path.levels
  obtain ⟨k₁,h₁⟩ := eventually_atTop.mp (high.eventually_gt_atTop 0)
  filter_upwards [inherited_patch (E:=E) L u simple sel D s p m hs hm hp hη,eventually_ge_atTop k₁]
    with k bought cutoff
  intro N n lo
  obtain ⟨S,hS,cost⟩ := bought N n lo
  refine ⟨S,hS,?_⟩
  intro j hk hj T h t V x H hH Q g w d U σ μ K hx small
  have hβ := (half_pos (h₁ (j+1) ((cutoff.trans hk).trans (Nat.le_succ _)))).trans_le (sel.represents N n (j+1) hj).band.1
  have hg : 0<g := inv_pos.mpr (Real.sqrt_pos.mpr hβ)
  have mass := haarPatch_mass hg.ne' hH x hx small
  have measured : 0<μ Set.univ := by simpa only [μ,Measure.restrict_apply_univ] using mass
  have hw := (norm_nonneg x).trans_lt hx
  have hδ : 0 ≤ d := mul_nonneg hH.le (div_nonneg (Real.rpow_nonneg hg.le _) hw.le)
  refine ⟨mass,?_⟩
  intro sd F hmF M hM bounds
  have geo := haarPatch_good (w:=w) (H:=H) hg.ne' x
  have priced := cost j hk hj T h t V μ measured x _ geo.1 H hH.le geo.2 F hmF M hM bounds
  simp only [show ∀ U : Config G _, x + (chartLog g U - x)=chartLog g U by intro v;abel] at priced
  exact priced.trans (mul_le_mul_of_nonneg_right (linear_tilt hδ sd) hM)

end YM.Integration.FVA1Physical.Wilson
