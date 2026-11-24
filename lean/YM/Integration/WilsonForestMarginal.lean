import YM.Integration.WilsonPhysicalRegisteredForestConditional

/-! Integration on one finite set of genuine forest coordinates gives a
bounded measurable reading of the entire complementary forest field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonForestMarginal
open Function Set MeasureTheory Metric Lattice RG Wilson Tree Precision PertExtension
open WilsonPhysicalRegisteredForestAction
open scoped Classical Topology
variable {G : Gauge} {c f : Side} {S : StepData c f}

def read (T : Forest S.ratio) (E : Finset T.Free) (a : Config G f → ℝ)
    (v : ({e : T.Free | e∉E}:Set T.Free)→G.El) : ℝ :=
  ∫ x, a (filled T E v x) ∂Chart.physical G (↥E)

theorem bounded (T : Forest S.ratio) (E : Finset T.Free) {a : Config G f → ℝ} (ha : Envelope a) :
    Envelope (read T E a) := by
  let V := (({e : T.Free | e∉E}:Set T.Free) → G.El)
  let U := (↥E → G.El)
  let μ := Chart.physical G (↥E)
  letI : IsProbabilityMeasure μ := by dsimp [μ,Chart.physical];infer_instance
  have fill : Measurable (fun z : V × U => a (filled T E z.1 z.2)) :=
    ha.meas.comp (T.continuous_drape.measurable.comp ((cut T E).symm.measurable.comp
      (measurable_snd.prodMk measurable_fst)))
  obtain ⟨B,h⟩ := ha.cost
  refine ⟨(fill.stronglyMeasurable.integral_prod_right' (ν:=μ)).measurable,B,fun v => ?_⟩
  change ‖∫ x, a (filled T E v x) ∂μ‖ ≤ B
  calc _ ≤ ∫ _ : U, B ∂μ := norm_integral_le_of_norm_le (integrable_const (μ:=μ) B)
           (ae_of_all _ (fun x => h (filled T E v x)))
       _ = B := by rw [integral_const,probReal_univ,one_smul]

end YM.Integration.WilsonForestMarginal
