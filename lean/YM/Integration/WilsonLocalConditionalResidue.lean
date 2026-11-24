import YM.Integration.WilsonLocalTerminalConditional
import YM.Integration.WilsonLocalPlaquetteForestBilling

/-! Actual and approximating conditional weights at a fixed exterior pivot.
The ratio approximant keeps the full original transition probability. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalConditionalResidue
open Function Finset Set Lattice RG Tree Wilson RG16 Precision PertExtension PertExtension.Series Push.BetaTransport
open PhysicalNext.Repeat.Legato WilsonPhysicalRegisteredForestAction WilsonReportingForestPivots
open WilsonLocalPlaquetteForest WilsonLocalPlaquetteField WilsonLocalPlaquetteAction
open scoped Classical BigOperators Matrix.Norms.Frobenius
variable {G:Gauge} {c f:Side} {S:StepData c f}

def position (T:Forest S.ratio) (B:Finset T.Free) (v:({e:T.Free|e∉moving T B}:Set T.Free)→G.El)
    (g:ℝ) (X:↥(moving T B)→G.Color) := restored T B v (fun i=>G.lieExp (g•X i))

def weight (P:ChartRatio G) (ρ:Config G f→ℝ) (T:Forest S.ratio) (B:Finset T.Free)
    (v:({e:T.Free|e∉moving T B}:Set T.Free)→G.El) (g:ℝ) (X:↥(moving T B)→G.Color) :=
  Chart.jacobian P (g•X)*ρ (position T B v g X)

def score (P:ChartRatio G) (p:ℕ) (β g:ℝ) (T:Forest S.ratio) (B:Finset T.Free)
    (v:({e:T.Free|e∉moving T B}:Set T.Free)→G.El) (X Y:↥(moving T B)→G.Color) :=
  let E:=moving T B
  let w:=background T B v
  (∑i:↥E,(WilsonLocalHaarOrder.polynomial P p g (X i)-WilsonLocalHaarOrder.polynomial P p g (Y i)))-
    β*booked (p+2) (support T E) (filled T E v w) 1 (extend T E w 1) (extend T E X 0) (extend T E Y 0) g

def fitted (P:ChartRatio G) (p:ℕ) (β g:ℝ) (K:Config G f→ℝ) (T:Forest S.ratio)
    (B:Finset T.Free) (v:({e:T.Free|e∉moving T B}:Set T.Free)→G.El) (X Y:↥(moving T B)→G.Color) :=
  K (position T B v g X)/K (position T B v g Y)*Real.exp (score P p β g T B v X Y)

def expense {ι:Type} [Fintype ι] (p:ℕ) (H W g:ℝ) (X Y:ι→G.Color) :=
  H*g^(p+1)*(∑i,(‖X i‖^(p+1)+‖Y i‖^(p+1)))+
  6*W*g^(p+1)*(∑i,(‖X i‖^(p+3)+‖Y i‖^(p+3)))

theorem counted {ι:Type} [Fintype ι] (p:ℕ) {H W g:ℝ} (hH:0≤H) (hW:0≤W) (hg:0≤g)
    (X Y:ι→G.Color) (A:ℝ) (bounds:∀i,‖X i‖≤A ∧ ‖Y i‖≤A) :
    expense p H W g X Y≤(Fintype.card ι:ℝ)*g^(p+1)*(2*H*A^(p+1)+12*W*A^(p+3)) := by
  unfold expense
  refine (add_le_add (mul_le_mul_of_nonneg_left (WilsonLocalPlaquetteForestBilling.uniform (p+1) X Y A bounds) (by positivity))
    (mul_le_mul_of_nonneg_left (WilsonLocalPlaquetteForestBilling.uniform (p+3) X Y A bounds) (by positivity))).trans_eq ?_
  ring

theorem positive (C:Family G) (made:C.Makes) (N per m:ℕ) (hm:m<N) (V:Config G (C.side m per)) :
    ∀U:Config G (C.side (m+1) per),0<(C.path.levels.clock.op m per).density (C.path.β N per (m+1)) U V ∧
      0<actualConditionalDensity C N per m V U := by
  let S:=C.path.levels.clock.op m per
  let β:=C.path.β N per (m+1)
  intro U
  have hk : 0<S.density β U V :=
    (inv_pos.mpr (noiseCost_pos S |β|)).trans_le (density_bounds S (C.path.levels.blocks m per).branches le_rfl U V).1
  exact ⟨hk,div_pos (mul_pos hk (Multi.AxisShift.chosen_positive made.wilson hm U))
    (Multi.AxisShift.chosen_positive made.wilson hm.le V)⟩

theorem relative {x y D:ℝ} (hx:0<x) (hy:0<y) (h:|Real.log x-Real.log y|≤D) :
    Real.exp (-D)*y≤x ∧ x≤Real.exp D*y := by
  rw [abs_le] at h
  have lo: -D+Real.log y≤Real.log x := by linarith only [h.1]
  have hi: Real.log x≤D+Real.log y := by linarith only [h.2]
  simpa only [Real.exp_add,Real.exp_log hx,Real.exp_log hy] using
    And.intro (Real.exp_le_exp.mpr lo) (Real.exp_le_exp.mpr hi)

end YM.Integration.WilsonLocalConditionalResidue
