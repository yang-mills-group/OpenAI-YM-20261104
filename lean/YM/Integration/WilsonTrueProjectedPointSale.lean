import YM.Integration.WilsonTrueProjectedFiledSource

/-! Sum the original signed returns on one physical child.  The fine film
contains the engineering factor of that child.  Neither endpoint averages
over the other preimages of its parent. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonTrueProjectedPointSale
open Function Finset MeasureTheory Lattice Wilson RG Labels Source Trace.Physical Trace.Physical.GermGraph
open PhysicalNext Repeat Legato Graces Roost Org
open WilsonTrueProjectedDualHistory WilsonTrueProjectedFiledTransfer WilsonTrueProjectedFiledSource
open scoped Classical BigOperators Matrix.Norms.Frobenius

variable {G : Gauge} (R : Run G) {d N p i : ℕ}
local notation "hi" => R.family.side (i+1) p
local notation "lo" => R.family.side i p

def charged (d : ℕ) (row : Config G hi → ℂ) : Config G hi → ℂ :=
  fun W => ((R.family.S.block i).val : ℂ)^d * row W

theorem restored (Ψ : ∀ j, Rep G (R.family.side j p)) (row : Config G hi → ℂ) :
    WilsonMeasuredOriginalColumnTransition.upper R (d:=d) (Ψ (i+1)) (charged R d row) =
      fun W => ((Ψ (i+1)).eval W : ℂ)*row W := by
  funext W
  let L : ℂ := (R.family.S.block i).val
  have hL : L ≠ 0 := by dsimp only [L]; exact_mod_cast (R.family.S.block i).pos.ne'
  change (L^d)⁻¹*(((Ψ (i+1)).eval W : ℂ)*(L^d*row W)) = _
  field_simp

theorem balance {T : Type*} [Fintype T] (Ψ : ∀ j, Rep G (R.family.side j p))
    {σ C Λ δ w : ℝ} (law : (Ψ i).Lawful σ C Λ δ w) (cut : i ≤ N)
    (fineEq : (Ψ (i+1)).eval = (R.family.path.rep N p (i+1)).eval)
    (lowerEq : (Ψ i).eval = (R.family.path.rep N p i).eval)
    (anchor : T) (film : T → Config G hi → ℂ) (emitted next : T → Config G lo → ℂ)
    (physical nominal : T → ℝ) (x : T → ℂ)
    (paid : ∀ t, Paid R (d:=d) (N:=N) Ψ (film t) (emitted t) (next t) (physical t) (nominal t))
    (intake : ∀ t, Integrable (WilsonMeasuredOriginalColumnTransition.upper R (d:=d)
      (Ψ (i+1)) (film t)) (prior G _)) :
    WilsonTrueProjectedDualHistory.Signed R (d:=d) (N:=N) Ψ (edge R
      (weighted (fun t => WilsonMeasuredOriginalColumnTransition.upper R (d:=d) (Ψ (i+1)) (film t)) x)
      (fun W => ((Ψ i).eval W : ℂ)*weighted next x W)) i
      (∑ t, ‖x t‖*(physical t+nominal t)) := by
  let columns (t : T) := edge R
    (WilsonMeasuredOriginalColumnTransition.upper R (d:=d) (Ψ (i+1)) (film t))
    (fun W => ((Ψ i).eval W : ℂ)*next t W)
  refine combine R Ψ law anchor columns (fun t => physical t+nominal t) ?_ ?_ x _ ?_ ?_
  · intro t
    obtain ⟨e,z,he,pe,hz,pz,hw,hy⟩ := paid t
    exact WilsonMeasuredOriginalColumnSigned.original R Ψ cut fineEq lowerEq law (columns t)
      (film t) (emitted t) (next t) (fine R ..) (fun W => congrFun (coarse R ..) W)
      e z he pe hz pz hw hy
  · intro t
    simpa only [columns,fine] using intake t
  · simp only [columns,fine]
  · funext W
    simp only [columns,coarse,weighted,Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => by ring

/-- All the paid grades at this child use the same complete original vacuum.
The mesh dilation cancels the inverse in the physical transition exactly once. -/
theorem original {T : Type*} [Fintype T] (Ψ : ∀ j, Rep G (R.family.side j p))
    {σ C Λ δ w : ℝ} (law : (Ψ i).Lawful σ C Λ δ w) (cut : i ≤ N)
    (fineEq : (Ψ (i+1)).eval = (R.family.path.rep N p (i+1)).eval)
    (lowerEq : (Ψ i).eval = (R.family.path.rep N p i).eval)
    (anchor : T) (row : T → Config G hi → ℂ) (emitted next : T → Config G lo → ℂ)
    (physical nominal : T → ℝ) (x : T → ℂ)
    (paid : ∀ t, Paid R (d:=d) (N:=N) Ψ (charged R d (row t))
      (emitted t) (next t) (physical t) (nominal t))
    (intake : ∀ t, Integrable (fun W => ((Ψ (i+1)).eval W : ℂ)*row t W) (prior G _)) :
    WilsonTrueProjectedDualHistory.Signed R (d:=d) (N:=N) Ψ (edge R
      (fun W => ((Ψ (i+1)).eval W : ℂ)*weighted row x W)
      (fun W => ((Ψ i).eval W : ℂ)*weighted next x W)) i (∑ t, ‖x t‖*(physical t+nominal t)) := by
  have fineIntegral (t : T) := (restored R (d:=d) Ψ (row t)).symm ▸ intake t
  have step := balance R Ψ law cut fineEq lowerEq anchor (fun t => charged R d (row t))
    emitted next physical nominal x paid fineIntegral
  convert step using 2
  funext W
  simp only [weighted,restored,Finset.mul_sum]
  exact Finset.sum_congr rfl fun t _ => by ring

end YM.Integration.WilsonTrueProjectedPointSale
