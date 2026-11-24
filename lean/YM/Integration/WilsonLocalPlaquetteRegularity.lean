import YM.Integration.WilsonLocalInheritedDensity

/-! Joint continuity of every genuine plaquette coefficient in its compact
pivots and all angular variables. The logarithmic Haar coefficient uses the
same native derivative at zero as the full density estimate. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalPlaquetteRegularity
open Set Function Finset Lattice RG Wilson Precision PertExtension PertExtension.Series Push.BetaTransport
open WilsonLocalPlaquetteTaylor
open scoped Classical Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {G:Gauge}

theorem diagonal {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f:E→ℂ) (hf:ContDiff ℝ ω f)
    (b z:E) (j:ℕ) : SignedChartTaylor.jet (fun h=>f (b+h)) z j =
      (j.factorial:ℝ)⁻¹ • (iteratedFDeriv ℝ j f b (fun _=>z)) := by
  let L:ℝ→L[ℝ]E:=(ContinuousLinearMap.id ℝ ℝ).smulRight z
  let F:=fun h=>f (b+h)
  have hf':ContDiffAt ℝ (j:ℕ) F (L 0):=(hf.comp (contDiff_const.add contDiff_id)).contDiffAt.of_le le_top
  change (j.factorial:ℝ)⁻¹ • (iteratedFDeriv ℝ j (F ∘ L) 0 (fun _=>1))=_
  rw [Push.Uniform.iter_lin_at (L:=L) hf']
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  simp [F,L,iteratedFDeriv_comp_add_left]

theorem coefficient (j:ℕ) : Continuous (fun a:Pivots G × Angles G=>row a.1 a.2 j) := by
  have d:Continuous (direction (G:=G)):=continuous_const.prodMk (continuous_const.prodMk continuous_id)
  have v:Continuous (fun a:Pivots G × Angles G=>iteratedFDeriv ℝ j (extension G) (frame a.1)) :=
    ((analytic (G:=G)).continuous_iteratedFDeriv (m:=j) le_top).comp (base.comp continuous_fst)
  have z:Continuous (fun a:Pivots G × Angles G=>fun _:Fin j=>direction a.2):=continuous_pi (fun _=>d.comp continuous_snd)
  refine (Complex.continuous_re.comp ((continuous_const (y:=(j.factorial:ℝ)⁻¹)).smul (v.eval z))).congr ?_
  intro a
  rw [row,←words,diagonal (extension G) analytic];rfl

theorem action (p:ℕ) (g:ℝ) : Continuous (fun a:Pivots G × Angles G=>WilsonLocalPlaquetteAction.polynomial p a.1 a.2 g) :=
  continuous_finsetSum _ (fun j _=>continuous_const.mul (coefficient j))

theorem haar (P:ChartRatio G) (p:ℕ) (g:ℝ) : Continuous (WilsonLocalHaarOrder.polynomial P p g) := by
  unfold WilsonLocalHaarOrder.polynomial Zone.eval
  apply continuous_finsetSum;intro j _
  have jet:Continuous (WilsonLocalHaarOrder.row P j):=continuous_const.mul
    ((iteratedFDeriv ℝ j (WilsonLocalHaarOrder.logarithm P) 0).cont.comp (continuous_pi (fun _=>continuous_id)))
  exact jet.const_smul (g^j)

end YM.Integration.WilsonLocalPlaquetteRegularity
