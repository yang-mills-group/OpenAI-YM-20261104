import YM.Integration.FVA1Physical.Wilson.KernelTilt
import YM.Integration.FVA1Physical.Wilson.CylinderOscillation

/-! A normalized, genuinely inherited block comparison. The arbitrary positive
reference measure can be restricted product Haar, including one with its exterior
held fixed. The price is uniform over the exterior, all volumes and all bounded
joint tests on the same block. -/
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

theorem continuous_bank {N n j k r : ℕ} (S : Scene C.path.levels n r) (T : Slices C.path.levels n)
    (hj : j ≤ N) (h : (traversal T hj).Room G) (t : (traversal T hj).Tags) {v : G.Color}
    (hS : Realized L.kin N n k r v S) (hk : k ≤ j) (p : ℕ) (hp : p ≤ r) (g : ℝ) :
    Continuous (boundaryBank L S T hj h t p g) := by
  have id : boundaryBank L S T hj h t p g = Aqua.ore (C.path.rep N n j) (S.Poly j) g p := by
    funext x
    have he := congrFun (sceneVacuumError_eq L S T hj h t hS hk hp g) x
    change Aqua.vine _ g x - Aqua.ore _ _ g p x = Aqua.vine _ g x - boundaryBank L S T hj h t p g x at he
    exact (sub_right_inj.mp he).symm
  rw [id]
  exact (Aqua.pure ..).continuous

/-- The independent incoming bank can replace the full non-bare physical incoming
action inside the next tagged block, for every bounded mixed insertion. The data
about the patch describe only where its Haar measure lives and its displacement;
there is no analytic comparison or bound on a vacuum denominator in the premises. -/
theorem inherited_patch (u : G.ColorIndex) (simple : G.Simple) (sel : C.path.Selected)
    (D : Docket C u L.O L.horizon L.kin) (s p m : ℕ) (hs : 6 ≤ s) (hm : 4 ≤ m)
    (hp : p+3 ≤ m) {η : ℝ} (hη : 0<η) :
    ∀ᶠ k : ℕ in atTop, ∀ N n, k ≤ N → ∃ S : Scene C.path.levels n (p+1),
      Realized L.kin N n k (p+1) (Lis.sun G u) S ∧
      ∀ j, k ≤ j → ∀ hj : j<N, ∀ (T : Slices C.path.levels n) (h : (traversal T hj).Room G)
        (tag : (traversal T hj).Tags) (V : Config G (C.side j n))
        (μ : Measure (Config G (C.side (j+1) n))) [IsFiniteMeasure μ], 0<μ Set.univ →
        ∀ (x : Positions (Primary (C.side (j+1) n) G))
          (v : Config G (C.side (j+1) n) → Positions (Primary (C.side (j+1) n) G)),
          AEMeasurable v μ → ∀ H : ℝ, 0 ≤ H →
          let Q := C.path.rep N n (j+1)
          let g := Heath.Stock.cue Q.beta
          let w := Mosaic.vol (C.path.levels.clock.hatBeta (j+1))
          let K := fun U=> (C.path.levels.clock.op j n).density Q.beta U V
          (∀ᵐ U ∂μ, palace (g • (x+v U))=U ∧ (∑ i, |v U i|) ≤ H ∧
            ∀ t∈Set.Icc (0:ℝ) 1, x+t • v U ∈ Metric.closedBall 0 w) →
          ∀ (F : Config G (C.side (j+1) n) → E), AEStronglyMeasurable F μ →
          ∀ M : ℝ, 0 ≤ M → (∀ᵐ U ∂μ, ‖F U‖ ≤ M) →
          ‖patchMean μ (fun U=>K U * Q.eval U) F - patchMean μ
            (fun U=>K U * Real.exp (boundaryBank L S T hj h tag p g (x+v U))) F‖ ≤ (Real.exp (2*(H*(g^((p:ℝ)+1-η)/w)))-1)*M := by
  have grows := Alto.broad.comp (Multi.Wage.hat_tend simple C.path.levels)
  obtain ⟨k₀,h₀⟩ := eventually_atTop.mp (grows.eventually_gt_atTop 0)
  filter_upwards [uniform_patch_oscillation L u simple sel D s p m hs hm hp hη,eventually_ge_atTop k₀] with k bought cutoff
  intro N n lo
  obtain ⟨S,hS,rows⟩ := bought N n lo
  refine ⟨S,hS,?_⟩
  intro j hk hj T h tag V μ iμ hmass x v hmV H hH Q g w K inside F hmF M hM bound
  let E₀ := sceneVacuumError L S T hj h tag p g
  let bank := boundaryBank L S T hj h tag p g
  let δ := H*(g^((p:ℝ)+1-η)/w)
  have hjk : k ≤ j+1 := hk.trans (Nat.le_succ _)
  have wide := h₀ (j+1) (cutoff.trans hjk)
  have hw : 0<w := div_pos wide (by norm_num)
  have hg : 0 ≤ g := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have unit : 0 ≤ g^((p:ℝ)+1-η)/w := div_nonneg (Real.rpow_nonneg hg _) hw.le
  have hδ : 0 ≤ δ := mul_nonneg hH unit
  have reg := continuous_bank L S T hj h tag hS hjk p (Nat.le_succ p) g
  apply kernel_tilt (C.path.levels.clock.op j n) (C.path.levels.blocks j n).branches Q.beta V _ 
    (Rep.envelope _ (sel.represents N n (j+1) hj).good)
    (SectorNext.Vacuum.strictly C.path sel N n (j+1) hj) (fun U=>bank (x+v U)) μ hmass
    (reg.measurable.comp_aemeasurable (aemeasurable_const.add hmV)) (E₀ x) δ hδ _ F hmF hM bound
  filter_upwards [inside] with U hu
  have priced := rows (j+1) hjk hj T h tag x (v U) hu.2.2
  have same : Real.log (Q.eval U) - bank (x+v U) = E₀ (x+v U) := by
    change Real.log (Q.eval U) - _ = Real.log (Q.eval (palace (g • (x+v U)))) - _
    rw [hu.1]
    rfl
  rw [same]
  exact priced.trans (mul_le_mul_of_nonneg_right hu.2.1 unit)

end YM.Integration.FVA1Physical.Wilson
