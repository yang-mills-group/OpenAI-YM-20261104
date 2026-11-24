import YM.Integration.FVA1Physical.Round2.CurrentFieldJets
import YM.Integration.FVA1Physical.Round2.ResponseGrowth
import YM.MSbar.Chord.Fig

/-! Polarizing the actual sparse Lie derivatives yields genuine Fréchet
operator bounds, with dimension-free constants on every selected set of bonds. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open MeasureTheory Lattice RG YM.Wilson Push.Local Push.Local.Kernel
open RGComparison.Core16 RGComparison.Core16.Spool MSbar MSbar.Bulk Next.Foundations
open AnalyticBridge.SectorAffine.Offset Planned.AtomRegular Finset
open scoped Classical Topology BigOperators ContDiff
variable {G : Gauge} {c f : Side}

def edgeProject (G : Gauge) (X : Edges c) : Directions G c →L[ℝ] Directions G c :=
  ContinuousLinearMap.pi fun e => if e∈X then
    ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Edge (Site c)=>G.Color) e else 0

theorem edgeProject_at (X : Edges c) (v : Directions G c) (e : Edge (Site c)) :
    edgeProject G X v e = if e∈X then v e else 0 := by
  by_cases h : e∈X <;> simp [edgeProject,h]

def tangentOrderPrice (G : Gauge) (u : ℝ) (k m : ℕ) (a : ℝ) :=
  (∑ i∈range (k+1),polarCost i) * (responsePrice G u k m 1 * a)

theorem reading_tangent_order (S : StepData c f) (R : Rep G f) (φ : Config G f → ℝ)
    (branch : S.patch.Branches S.kernel G) (vac : Envelope R.eval)
    (pos : ∀ U, 0 < R.eval U) (field : Envelope φ) {a : ℝ} (cap : ∀ U, |φ U| ≤ a)
    (X : Edges c) (V : Config G c) (k : ℕ) :
    Through k (fun z=>expect S R (increment V (edgeProject G X z)) φ) 0
      (tangentOrderPrice G (R.beta*S.kernel.penalty) k X.card a) := by
  let E:=fun W=>expect S R W φ
  let P:=edgeProject G X
  let g:=fun z=>E (increment V (P z))
  let C:=responsePrice G (R.beta*S.kernel.penalty) k X.card 1 * a
  have hd:=vac.integrable (prior G f)
  have hi:=(field.mul vac).integrable (prior G f)
  have chart : Chart k E V := by
    have hN:=smooth_pass S R.beta Finset.univ branch hi V k
    have hD:=smooth_pass S R.beta Finset.univ branch hd V k
    have hp:=pass_pos S R.beta Finset.univ branch V hd pos
    apply (show Chart k (S.push R.beta (φ*R.eval)) V from hN).div
      (show Chart k (S.push R.beta R.eval) V from hD)
    simpa [Work.G07.at_zero_increment] using (show 0 < S.push R.beta R.eval V from hp).ne'
  have h0 : ContDiffAt ℝ k (E ∘ increment V) (P 0) := P.map_zero.symm ▸ chart
  have hg : ContDiffAt ℝ k g 0 := h0.comp 0 P.contDiff.contDiffAt
  have c0 : 0 ≤ C := mul_nonneg (responsePrice_nonnegative G _ k X.card zero_le_one)
    ((abs_nonneg (φ 1)).trans (cap 1))
  refine ⟨hg,?_⟩
  intro i ik
  have smooth:=hg.of_le (Nat.cast_le.mpr ik)
  have form : ‖iteratedFDeriv ℝ i g 0‖ ≤ polarCost i*C := by
    refine op_polar (Analysis.sym_Jet smooth) c0 ?_
    intro w hw
    have wh:=current_reading_jets S R φ branch vac pos field cap X V k zero_le_one
      (List.replicate i (P w)) (by simpa using ik)
      (fun v hv e he=>by rw [(List.mem_replicate.mp hv).2,edgeProject_at,if_neg he])
      (fun v hv e he=>by
        rw [(List.mem_replicate.mp hv).2,edgeProject_at,if_pos he]
        exact (norm_le_pi_norm w e).trans hw)
    have direction:=leftDerivs_diag V (P w) E i 0
    rw [zero_smul,Work.G07.at_zero_increment] at direction
    change ‖leftDerivs E (List.replicate i (P w)) V‖ ≤ C at wh
    rw [direction] at wh
    rw [← iteratedDeriv_on_line smooth]
    simpa only [g,map_smul] using wh
  exact form.trans (mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun i _=>(zero_le_one.trans (polar_one i))) (Finset.mem_range.mpr (by omega : i<k+1))) c0)

end YM.Integration.FVA1Physical.Round2.Curvature
