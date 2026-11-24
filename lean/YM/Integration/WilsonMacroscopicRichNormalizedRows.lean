import YM.Integration.WilsonMacroscopicRichLastResponse

/-! Differentiate the complete last physical conditional, retaining the response of its same-state normalization inside the joint Haar integral. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichNormalizedRows
open Function MeasureTheory Set Lattice Wilson RG Source Push.Local Push.Local.Kernel PhysicalNext.Repeat.Legato RGComparison.Core16
open scoped Classical BigOperators Topology
open private observe pass_observe from YM.Push.LOCAL_SPLITTING.Marginal
variable {G : Gauge} {c f : Side}

def mixture (S : StepData c f) (U : Config G f) : C(Config G c,ℝ) →L[ℝ] ℝ :=
  ∑ t,S.likelihood U t • ContinuousMap.evalCLM ℝ (S.prediction U t)

theorem evaluated (S : StepData c f) (U : Config G f) (g : C(Config G c,ℝ)) :
    mixture S U g = weights S U g := by simp [mixture,weights]

def kernel (S : StepData c f) (β : ℝ) (D : Config G f → ℝ) (V : Config G c) : C(Config G c,ℝ) :=
  (S.push β D V)⁻¹ • noiseLift S β Finset.univ V

theorem chart (S : StepData c f) (hS : S.patch.Branches S.kernel G) (β : ℝ)
    (D : Config G f → ℝ) (hD : Integrable D (prior G f)) (pos : ∀ V, 0 < S.push β D V)
    (V : Config G c) (k : ℕ) : Chart k (kernel S β D) V := by
  have low : Chart k (S.push β D) V := smooth_pass S β Finset.univ hS hD V k
  have nz : (S.push β D ∘ increment V) (0 : Directions G c) ≠ 0 := (pos _).ne'
  exact (low.inv nz).smul (smooth_lift S β Finset.univ V k)

theorem conditional (S : StepData c f) (β : ℝ) (D : Config G f → ℝ) (U : Config G f) :
    (fun W => S.density β U W / S.push β D W) = mixture S U ∘ kernel S β D := by
  funext W
  change _ = mixture S U ((S.push β D W)⁻¹ • noiseLift S β Finset.univ W)
  rw [map_smul,evaluated,smul_eq_mul,div_eq_inv_mul]
  congr 1
  change (∑ t,S.likelihood U t * S.noise β (S.prediction U t) W) = ∑ t,S.likelihood U t * noiseLift S β Finset.univ W (S.prediction U t)
  simp_rw [lifted]; rfl

private theorem moved (S : StepData c f) (hS : S.patch.Branches S.kernel G) (β : ℝ)
    (D : Config G f → ℝ) (X : Config G f → ℂ) (hX : Integrable X (prior G f)) :
    (fun W => (S.push β D W)⁻¹ • S.push β X W) = observe S hS hX ∘ kernel S β D := by
  funext W
  change _ = observe S hS hX ((S.push β D W)⁻¹ • noiseLift S β Finset.univ W)
  rw [map_smul]; exact congrArg ((S.push β D W)⁻¹ • ·) (congrFun (pass_observe S β Finset.univ hS hX) W)

/-- The true signed derivative of the normalized transition, including the reciprocal vacuum, acts on the original upper field. -/
theorem integral (S : StepData c f) (hS : S.patch.Branches S.kernel G) (β : ℝ)
    (D : Config G f → ℝ) (hD : Integrable D (prior G f)) (pos : ∀ V, 0 < S.push β D V)
    (X : Config G f → ℂ) (hX : Integrable X (prior G f))
    (l : List (Directions G c)) (V : Config G c) :
    leftDerivs (fun W => (S.push β D W)⁻¹ • S.push β X W) l V =
      ∫ U, leftDerivs (fun W => S.density β U W / S.push β D W) l V • X U ∂prior G f := by
  have smooth := chart S hS β D hD pos V l.length
  rw [moved S hS β D X hX,left_linear _ _ smooth le_rfl]
  change (∫ U, weights S U ⇑(leftDerivs (kernel S β D) l V : C(Config G c,ℝ)) • X U ∂prior G f) = _
  apply integral_congr_ae; filter_upwards [] with U
  rw [conditional S β D U,left_linear _ _ smooth le_rfl,evaluated]

/-- One original selected date and its full measured matter, at every held field and in all ordered directions. -/
theorem original (R : Run G) {u N p : ℕ} (T : Slices R.family.path.levels p) (live : u < N)
    (Y : Config G (R.family.side N p) → ℂ) (ct : Continuous Y)
    (l : List (Directions G (R.family.side u p))) (V : Config G (R.family.side u p)) :
    let H := R.family.path
    let S := H.levels.clock.op u p
    let β := H.β N p (u+1)
    let X := (traversal T live).weighted (line H p (u+1) N) Y
    leftDerivs ((traversal T live.le).conditioned (line H p u N) Y) l V =
      ∫ U, leftDerivs (fun W => S.density β U W / (H.rep N p u).eval W) l V • X U ∂prior G _ := by
  intro H S β X
  let D := (H.rep N p (u+1)).eval
  have di : Integrable D (prior G _) := by
    change Integrable (H.rep N p (u+1)).eval _
    rw [←vacuum_eq T R.makes.wilson live]
    exact Descent.output_integrable (traversal_ok T live) _ (bare_integrable _)
  have den : (H.rep N p u).eval = S.push β D := (R.makes.wilson.steps N p u live).1
  have lo : (traversal T live.le).vacuum (G:=G) (line H p u N) = S.push β D :=
    (vacuum_eq (m:=u) T R.makes.wilson live.le).trans den
  have hi : (traversal T live.le).weighted (line H p u N) Y = S.push β X := weighted_step T Y live
  have pos V : 0 < S.push β D V := lo ▸ Descent.positive (line H p u N) (traversal_ok T live.le) V
  change leftDerivs (fun W => ((traversal T live.le).vacuum (G:=G) (line H p u N) W)⁻¹ • (traversal T live.le).weighted (line H p u N) Y W) l V = _
  rw [lo,hi,den]
  exact integral S (H.levels.blocks u p).branches β D di pos X (weighted_integrable T live Y ct) l V

end YM.Integration.WilsonMacroscopicRichNormalizedRows
