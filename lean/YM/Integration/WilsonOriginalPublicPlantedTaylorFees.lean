import YM.Integration.WilsonOriginalPublicPlantedTaylorTest

/-! The coefficient order can be chosen after a fixed finite physical restoration and
before the optical collar. All later raw orders use the same lower Taylor order. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonOriginalPublicPlantedTaylorFees
open Filter Set Finset Function Metric MeasureTheory Lattice Maxwell XSpace XSpace.Cirrus XSpace.Normalize
open XSpace.Structure1 FVA2 FVA2.Register FVA2.Scale MS MS.Land PowerSeries
open WilsonOriginalPublicPlantedTaylorTest (tested)
open scoped Topology BigOperators Classical

theorem restore {t W L δ:ℝ}(positive:0<t)(small:t≤1)(fee:0≤W)(tol:0≤δ)
    (E p J:ℕ)(budget:E+p≤J)(paid:t^E*W≤L):
    W*(δ*t^J)≤L*δ*t^p:=by
  calc
    _≤W*(δ*t^(E+p)):=mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one positive.le small budget) tol) fee
    _=t^E*W*(δ*t^p):=by rw [pow_add];ring
    _≤L*(δ*t^p):=mul_le_mul_of_nonneg_right paid (mul_nonneg tol (pow_nonneg positive.le _))
    _=_:=by ring

theorem addition {I:Type}[Fintype I](w Y:I→ℂ)(m:I→ℝ)(e:ℝ)(paid:∀a,‖Y a‖ ≤ m a*e):
    ‖∑a,w a*Y a‖≤(∑a,‖w a‖*m a)*e:=by
  rw [sum_mul]
  apply (norm_sum_le ..).trans (sum_le_sum _)
  intro a _
  rw [norm_mul,mul_assoc]
  exact mul_le_mul_of_nonneg_left (paid a) (norm_nonneg _)

variable {G:Gauge}(Z:WilsonPrescription G){sg:G.Simple}
    {M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}{T:Prescription (Press.portDeck G)}
    {dial:Bool}(H:Main.Match Z sg M T dial)(β:Local.Physical.Deck G){n d:ℕ}
    {K:Set (Points n)}(compact:IsCompact K)(apart:K⊆conf n)
    (l:Filter ℝ){t:ℝ→ℝ}(pos:∀ᶠ r in l,0<t r)(small:Tendsto t l (𝓝 0))
    {I:Type}[Fintype I](v:I→Tags G d n)

def wage (M:Mesh)(w:I→ℂ)(φ:I→Test n):ℝ:=
  ∑a,‖w a‖*WilsonPositionProgramTrialCellVariation.mass M (φ a)

def bill (j q:ℕ)(w:I→ℂ)(φ:I→Test n)(u:ℝ):ℂ:=∑a,w a*tested Z β (v a) j q (φ a) u

include H compact apart pos small in
theorem original (E p J:ℕ)(room:E+p≤J)(Q:ℕ)(order:J≤Q)(D:ℕ)(C:ℝ){δ:ℝ}(toll:0<δ):
    ∃j₀:ℕ,∀ᶠ r in l,∀j≥j₀,(j:ℝ)≤C*(-Real.log (t r))^D →
      ∃P:Handoff.Directory Z j (Handoff.Directory.budget G n d+Q),
      ∀(φ:I→Test n),(∀a,tsupport (φ a)⊆K) → ∀(w:I→ℂ)(u:ℝ),|u|≤8*t r →
      (∀a,∀q≤Q,tested Z β (v a) j q (φ a) u=
        ∑k∈range (q+1),WilsonPositionRawEpoch.row Z P d (φ a) (v a) k*(u:ℂ)^k) ∧
      ‖bill Z β v j Q w φ u-bill Z β v j J w φ u‖≤wage (Z.run.step j) w φ*(δ*(t r)^J) ∧
      ∀L,(t r)^E*wage (Z.run.step j) w φ≤L →
        ‖bill Z β v j Q w φ u-bill Z β v j J w φ u‖≤L*δ*(t r)^p:=by
  classical
  choose j₀ available using fun a=>WilsonOriginalPublicPlantedTaylorTest.original Z H β compact apart l pos small
    (v a) J Q order D C toll
  refine ⟨univ.sup j₀,?_⟩
  filter_upwards [Filter.eventually_all.mpr available,pos,
    small.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num))] with r allRows hr cold
  intro j deep clock
  obtain ⟨P⟩:=H.packets j (Handoff.Directory.budget G n d+Q)
  refine ⟨P,?_⟩
  intro φ supports w u close
  have individual(a:I):=allRows a j ((le_sup (f:=j₀) (mem_univ a)).trans deep) clock P le_rfl
    (φ a) (supports a) u close
  have total:‖bill Z β v j Q w φ u-bill Z β v j J w φ u‖≤wage (Z.run.step j) w φ*(δ*(t r)^J):=by
    unfold bill wage
    rw [←sum_sub_distrib]
    simp_rw [←mul_sub]
    exact addition _ _ _ _ individual
  refine ⟨fun a q hq=>WilsonOriginalPublicPlantedTaylorTest.printed Z β (v a) P q (by omega) (φ a) u,
    total,?_⟩
  intro L spent
  apply total.trans (restore hr cold.le _ toll.le E p J room spent)
  exact sum_nonneg fun a _=>mul_nonneg (norm_nonneg _) (mul_nonneg
    (pow_nonneg (Z.run.step j).positive.le _) (sum_nonneg fun _ _=>norm_nonneg _))

end YM.Integration.WilsonOriginalPublicPlantedTaylorFees
