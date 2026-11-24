import YM.LocalLTE.Port.Panels
/-! # supports and aggregation.C helper -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Port
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus FrameBox Cabana Push
open Progress.DirectedRecipe MergeProof Menu Marker Accent Overlay
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G : Gauge}{c f : Side}{Q : Rep G f} {S:StepData c f} {σ κ Λ μ' w t v : ℝ}
variable {V I J : Type}[DecidableEq V][Fintype V] {R:Marker.Census V}(B:Bands R Q)(r:V→ℝ) (hr:∀ i,0<r i) (o:V→Site f)
open Extra.Trajectories Push.AbsoluteSums
variable [Fintype J]
local notation "P"=> Q.p
variable (p:BudgetPoint)(X:J→Support f)(K:J→ R.Mode)(Y:I→J)(b:I→ℝ) (hb:SumBudget (fun i=>Poly.toll r (K (Y i))*p.mass (X (Y i)) (b i)) Λ) (ha:∀ i,0≤b i)
include hb hr ha
local notation "B'"=> (fun i:I=> Poly.toll r (K (Y i))*p.mass (X (Y i)) (b i))
omit [Fintype V] [Fintype J] in
lemma ember (j:J) : Summable (fun i:{i//Y i=j}=> b i.val):=by
    let q:= fun i:{i//Y i=j}=> B' i.val
    have he(i:{i//Y i=j}): q i = Poly.toll r (K j) * p.mass (X j) (b i.val):= by unfold q; dsimp only;rw [i.property]
    have hz := hb.2.1.comp_injective (show Injective (Subtype.val : {i//Y i=j}→I) from Subtype.val_injective)
    have hv: Summable (fun i:{i//Y i=j}=> (Poly.toll r (K j))⁻¹ * q i):= hz.mul_left _
    exact hv.of_nonneg_of_le (fun i=> ha i.val) (fun i=> by rw [he,inv_mul_cancel_left₀ (Poly.worth hr _|>.ne')]; exact p.loMass _ _ (ha _))
omit hr ha [Fintype V] in
lemma wholeQ : (∑ i:J,Poly.toll r (K i)*p.mass (X i) (cram Y b i)) ≤ Λ:=by
    let u (i:I):= B' i; have hx:= heavy Y hb.2.1
    have he : ∑ j:J, cram Y u j≤Λ:=by rw [← tsum_fintype (L:=SummationFilter.unconditional _), hx.tsum_eq]; exact hb.2.2
    have ht(i):Poly.toll r (K i)*p.mass (X i) (cram Y b i)=cram Y u i:=by unfold u BudgetPoint.mass cram; rw [← tsum_mul_left, ← tsum_mul_left]; apply tsum_congr; intro i; dsimp only; rw [i.property]
    simp_rw [ht]; exact he
omit [Fintype V] in
lemma everyone : Summable b:=by
    have hf j := Port.ember r hr p X K Y b hb ha j
    let W:= Equiv.sigmaFiberEquiv Y; let g i:= b (W i)
    have hg:Summable g:= (summable_sigma_of_nonneg (show ∀ i,0 ≤ g i from fun i=> ha _)).2 ⟨hf,.of_finite⟩
    exact W.summable_iff.mp hg
omit hr ha hb
-- slots.Two-phase describes value + fidelity (zero too)
end YM.LocalLTE.Port
