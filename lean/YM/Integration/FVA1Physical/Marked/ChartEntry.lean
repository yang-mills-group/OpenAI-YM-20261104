import YM.Integration.FVA1Physical.Marked.ChartBank

/-! Physical exponential-chart entries for the exact paid grade-zero density.
The constant headline disappears in positive order; every derivative includes
the physical coupling once per coordinate. -/
set_option autoImplicit false
set_option maxHeartbeats 1350000
noncomputable section
namespace YM.Integration.FVA1Physical.Marked
open Function Filter Finset Lattice RG YM.Wilson Source Labels Push Push.Uniform
open MSbar MSbar.Lis MSbar.Midpoint MSbar.RawP MSbar.Wave MSbar.Rolling
open AnalyticBridge.SectorAffine.Offset PhysicalNext.Repeat Push.AbsoluteSums
open scoped Classical BigOperators Topology ContDiff
variable {G:Gauge} {n:Side} {R:Rep G n} {o:Site n} {F:Frame G 0} {A:Hol G}
local notation "E" => Positions (Primary n G)

theorem chart_entry {Q:Coefficient F n} (D:SectionData F) (form:Q.Format o A R)
    {κ C:ℝ} (bill:Q.remBound o R κ C) (field:Config G n→ℝ)
    {g α:ℝ} {x:E} (small:‖g•x‖<1) (clear:palace (g•x)∈Boulevard.sunny R.p)
    (ident:(fun V=>(field V:ℂ)) =ᶠ[𝓝 (palace (g•x))] Q.exponentialEntry o D R)
    {k:ℕ} (order:k≤R.p.order) (α0:0≤α) (room:α*k*(6*R.p.B+2:ℝ)≤R.p.supportExponent) :
    ContDiffAt ℝ k (fun z=>field (postcard G n g z)) x ∧
      ∀ j, 0<j → j≤k → ∀ w:Fin j → Primary n G,
      ‖YM.Push.Uniform.entry (fun z=>field (postcard G n g z)) x w‖ ≤
        |g|^j*(earnE R.p G k*C)*Real.exp (-α*spanSites (Measuring.chart n G) o w) := by
  obtain ⟨a,b,_ha,hb,ab,_,⟨v,credit,limits⟩,_⟩:=bill
  let f:ℕ → Config G n → ℝ:=fun i=>Complex.reCLM ∘ Q.regular i
  let S:=Q.support
  let price:=earnE R.p G k
  have data (i:ℕ) : R.p.Regular (S i) (f i) ∧ R.p.supBounds o (S i) (f i) (v i) := by
    refine ⟨AnalyticBridge.VerifiedReset.regular_mapped Complex.reCLM (form.smooth i),⟨(limits i).1,?_⟩⟩
    intro U hu dirs length bounds
    change ‖leftDerivs (Complex.reCLM ∘ Q.regular i) dirs U‖ ≤ _
    rw [Push.Local.left_linear Complex.reCLM dirs ((form.smooth i).smooth U hu) length]
    exact (Complex.abs_re_le_norm _).trans ((limits i).2 U hu dirs length bounds)
  let series:E→ℝ:=fun z=>∑' i,Program (f i) z
  obtain ⟨smooth,decay⟩:=chart_bank (fun i=>(data i).1) (fun i=>(data i).2)
    form.origin credit order α0 room small clear
  let Y:=fun z:E=>field (palace z)
  have hc:Continuous (palace (G:=G) (c:=n)) := by
    apply continuous_pi
    intro e
    exact (G.lieExp_cont.comp ((continuous_apply e).comp (panel G n).continuous)).mul continuous_const
  have identity:Y=ᶠ[𝓝 (g•x)] (fun z=>(Q.x 0).re+series z) := by
    filter_upwards [hc.continuousAt.eventually ident,
      hc.continuousAt.eventually ((Boulevard.sky R.p).mem_nhds clear)] with z eq hz
    have clean i : Q.maskedTerm R i (palace z)=Q.regular i (palace z) := by
      apply masked_eq
      unfold Healthy
      rw [Boulevard.smoky hz];simp
    have total:Summable (fun i=>Q.regular i (palace z)) := by
      have data:=(complex_termwise form.smooth limits credit).sums [] (Nat.zero_le _) (palace z) hz
      exact data
    have realSum:=Complex.reCLM.map_tsum total
    rw [LocalLTE.Concourse.center_entry,tsum_congr clean] at eq
    exact (congrArg Complex.re eq).trans (congrArg ((Q.x 0).re+·) realSum)
  have hY: ContDiffAt ℝ k Y (g•x) := (contDiffAt_const.add smooth).congr_of_eventuallyEq identity
  have smoothScaled : ContDiffAt ℝ k (fun z:E=>Y (g•z)) x :=
    hY.comp x ((g • ContinuousLinearMap.id ℝ E).contDiff.contDiffAt)
  refine ⟨smoothScaled,?_⟩
  intro j jp jk w
  have dY:=hY.of_le (Nat.cast_le.mpr jk)
  have dS:=smooth.of_le (Nat.cast_le.mpr jk)
  have base : YM.Push.Uniform.entry Y (g•x) w=YM.Push.Uniform.entry series (g•x) w := by
    unfold YM.Push.Uniform.entry
    rw [(identity.iteratedFDeriv ℝ j).eq_of_nhds]
    change iteratedFDeriv ℝ j ((fun _:E=>(Q.x 0).re)+series) (g•x) _=_
    rw [iteratedFDeriv_add_apply (show ContDiffAt ℝ j (fun _:E=>(Q.x 0).re) (g•x) from contDiffAt_const) dS,
      iteratedFDeriv_const_of_ne jp.ne' (Q.x 0).re, Pi.zero_apply,zero_add]
  have scale : YM.Push.Uniform.entry (fun y:E=>Y (g•y)) x w=g^j*YM.Push.Uniform.entry Y (g•x) w := by
    let L:E→L[ℝ] E:=g • ContinuousLinearMap.id ℝ E
    change iteratedFDeriv ℝ j (Y ∘ L) x _=_
    rw [iter_lin_at (show ContDiffAt ℝ j Y (L x) from dY),ContinuousMultilinearMap.compContinuousLinearMap_apply]
    change iteratedFDeriv ℝ j Y (g•x) (fun i=>g • bolt (w i))=_
    rw [ContinuousMultilinearMap.map_smul_univ,Finset.prod_const,card_univ,Fintype.card_fin]
    rfl
  change ‖YM.Push.Uniform.entry (fun y:E=>Y (g•y)) x w‖ ≤ _
  rw [scale,base,norm_mul,Real.norm_eq_abs,abs_pow]
  have cap:=decay j jk w
  have bound:price*a ≤ price*C := mul_le_mul_of_nonneg_left ((le_add_of_nonneg_right hb).trans ab) (floorP G R.p k)
  exact (mul_le_mul_of_nonneg_left (cap.trans (mul_le_mul_of_nonneg_right bound (Real.exp_pos _).le))
      (pow_nonneg (abs_nonneg g) _)).trans_eq (by ring)
end YM.Integration.FVA1Physical.Marked
