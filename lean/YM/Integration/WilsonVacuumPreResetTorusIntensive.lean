import YM.Integration.WilsonVacuumPreResetTorusContraction
import YM.Integration.WilsonVacuumPreResetTorusMoment

/-! Intensive finite-volume evaluation of the full positive-rank polynomial
on a bounded family of real physical angles before the periods increase. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetTorusIntensive
open Filter Function Finset Lattice Wilson WilsonCoeffUV WilsonCoeffUV.Bank
open Matrix RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open WilsonVacuumPreResetTorusContraction WilsonVacuumPreResetTorusMoment
open scoped Classical BigOperators Topology
variable {α I:Type*}[Fintype α]{l:ℕ}{f:Filter I}

theorem joined_limit (P:raw α ℝ (l+1))(h:Yields P 0)(n:I→Side)(grows:Tendsto n f atTop)
    (H:∀p,(Fin (l+1) → (Site (n p) × α)) → ℂ){D:ℝ}(bounded:∀p X,‖H p X‖≤D):
    Tendsto (fun p=>(Fintype.card (Site (n p)):ℝ)⁻¹ • joined (P (n p)) (H p)) f (𝓝 0):=by
  have roots (a:α):Tendsto (fun p=>charge (P (n p)) 0 a) f (𝓝 0):=by
    have root:=WilsonVacuumPreResetTorusMoment.original P h (0,a) 0
    simpa [charge,term,foldUnder,Function.comp_def] using root.comp grows
  have sales:Tendsto (fun p=>D*∑a,charge (P (n p)) 0 a) f (𝓝 0):=by
    simpa only [sum_const_zero,mul_zero] using (tendsto_finsetSum univ (fun a _=>roots a)).const_mul D
  apply squeeze_zero_norm' _ sales
  filter_upwards [grows.eventually h.strolls] with p moves
  have pos:0<(Fintype.card (Site (n p)):ℝ):=by positivity
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr pos)]
  calc
    _≤(Fintype.card (Site (n p)):ℝ)⁻¹ *
      ((Fintype.card (Site (n p)):ℝ)*(D*∑a,charge (P (n p)) 0 a)):=
      mul_le_mul_of_nonneg_left (absolute_bound _ moves _ (bounded p)) (inv_nonneg.mpr pos.le)
    _=_:=inv_mul_cancel_left₀ pos.ne' _

theorem original (P:raw α ℝ (l+1))(h:Yields P 0)(n:I→Side)(grows:Tendsto n f atTop)
    (z:∀p,(Site (n p) × α) → ℝ){D:ℝ}(bounded:∀p x,‖z p x‖≤D):
    Tendsto (fun p=>(Fintype.card (Site (n p)):ℝ)⁻¹ •
      ((MvPolynomial.eval (z p) (Blue.paint (l+1) (P (n p))):ℝ):ℂ)) f (𝓝 0):=by
  let H (p:I)(X:Fin (l+1) → (Site (n p) × α)):ℂ:=∏i,(z p (X i):ℂ)
  have bound (p:I)(X:Fin (l+1) → (Site (n p) × α)):‖H p X‖≤D^(l+1):=by
    dsimp only [H]
    rw [norm_prod]
    calc
      _ ≤ ∏_i:Fin (l+1),D:=prod_le_prod (fun i _=>norm_nonneg _) (fun i _=>by simpa using bounded p (X i))
      _ = _:=by simp
  simpa only [painted,H] using joined_limit P h n grows H bound

end YM.Integration.WilsonVacuumPreResetTorusIntensive
