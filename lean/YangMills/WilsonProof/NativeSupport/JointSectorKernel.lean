import YangMills.WilsonProof.NativeSupport.JointChart
import YangMills.WilsonProof.NativeSupport.JointTicketMarginal

/-! Reassemble the planted series at a single original sector. Every term uses the
same bounded measurements of the same original predictor bonds. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.JointTicket
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.BetaTransport Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Contract Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse Coat Matter
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus JointCoat ProbabilityTheory Poll Pond
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P : Teller G} {T : Tube G S}
    {F : Forest S.ratio} {R : Rep G f} {W μ C : ℝ}
    {Q : ConnectedActivityE6.Target G P} {o : ConnectedActivityE6.Target.Order G W}
variable (K : Team R) (X : Coat T F) (H : Cash W X.x μ L Q o C T R)
variable (width : X.width=o.K) (k : Finset ℕ) (J : Finset (Bond c)) (h : Bond c→ℝ→ℝ)

private theorem issue_injective (Y : Finset (Stores S)) (k : Finset ℕ) : Injective (issue Y k) := by
  intro x y eq
  apply Prod.ext
  · simpa [issue,blaze] using congr_arg blaze eq
  simpa only [issue,toRight_disjSum,toLeft_disjSum] using
    congr_arg (fun z : Molecule S => z.toRight.toRight.toLeft) eq

private theorem mul_integrable {α : Type*} [MeasurableSpace α] {D : Measure α} {u v : α→ℝ}
    (hu : Integrable u D) (hv : Measurable v) (h1 : ∀ s,‖v s‖≤1) :
    Integrable (fun s => u s*v s) D :=
  hu.norm.mono' (hu.aestronglyMeasurable.mul hv.aestronglyMeasurable)
    (ae_of_all D fun s => norm_mul _ _ |>.trans_le (mul_le_of_le_one_right (norm_nonneg _) (h1 s)))

theorem sampled_unit (unit : ∀ b∈J,∀ e∈Set.Icc 0 (linkCap S),‖h b e‖≤1)
    (s : F.Slice G) : ‖X.sampled J h s‖≤1 := by
  unfold Coat.sampled
  rw [norm_prod]
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _) fun b bJ =>
    unit b bJ _ ⟨(link_estimate S).nonneg _,(link_estimate S).bound _⟩

include H width in
theorem sector_chart (manifest : X.manifest) (Y : Finset (Stores S))
    (layout : Layout X.seeds Q.halo X.B Y) (sealed : Contract.sealed R k)
    (hm : ∀ b∈J,Measurable (h b)) :
    (∫ u,K.realP X (X.shifted u) k W * X.sampled J h (X.shifted u) ∂X.stages) =
      X.tribute R Q.table*∫ z,K.salary X k W o.a Q.table Y z *
        ∏ b∈J,h b (energy X (X.liftA R.beta z) b) ∂X.dice := by
  let g z := ENNReal.ofReal (X.thetaRef z)
  have hd : X.dice = volume.withDensity g := Poll.sweep_pdf (H.laws.data.localP F X rfl width manifest).sails.fullC
  have hg : Measurable g := by unfold g thetaRef dotProduct; fun_prop
  rw [X.measured_chart K H width k J h hm,hd,integral_withDensity_eq_integral_toReal_smul hg
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top),←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with z
  rw [K.approved X k H manifest width z layout sealed]
  unfold g tribute
  rw [ENNReal.toReal_ofReal (show 0≤X.thetaRef _ by unfold thetaRef bell; positivity),smul_eq_mul]
  ring

include H width in
theorem measured_series (manifest : X.manifest) (Y : Finset (Stores S))
    (layout : Layout X.seeds Q.halo X.B Y) (hm : ∀ b∈J,Measurable (h b))
    (unit : ∀ b∈J,∀ e∈Set.Icc 0 (linkCap S),‖h b e‖≤1) :
    let D := (F.order G).prod X.dice
    let f (s : F.Slice G×Air f G) := K.salary (X.wrapY s.1) k W o.a Q.table Y s.2 *
      ∏ b∈J,h b (lifted X R.beta b s)
    Integrable f D ∧ HasSum (fun t => ∫ s,raw (W:=W) K X k (issue Y k t)
      o.a Q.table Q.halo J h s ∂D) (∫ s,f s ∂D) := by
  intro D f'
  let g t := raw (W:=W) K X k (issue Y k t) o.a Q.table Q.halo J h
  let v (s : F.Slice G×Air f G) := ∏ b∈J,h b (lifted X R.beta b s)
  have hv : Measurable v := Finset.measurable_fun_prod J fun b bJ =>
    (hm b bJ).comp (measurable_lifted X H width b)
  have h1 s : ‖v s‖≤1 := by
    unfold v
    rw [norm_prod]
    exact Finset.prod_le_one (fun _ _ => norm_nonneg _) fun b bJ => unit b bJ _ (in_band X _ b s)
  refine ⟨mul_integrable (K.tithes X k H width manifest Y layout).1 hv h1,?_⟩
  have hb : Summable H.text := Summable.sum _ (hasSum_fintype _).summable (budgets_arr H)
  have hs := (Team.crowns_has K.weight (K.signs S) hb H.positive).comp_injective (issue_injective Y k)
  have paid t := raw_price K X H width manifest k (issue Y k t) J h hm unit
  have hz : Summable (fun t=>∫ s,‖g t s‖ ∂D) :=
    hs.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) fun t => (paid t).2
  have hx := hasSum_integral_of_summable_integral_norm (fun t => (paid t).1) hz
  have whole s : (∑' t,g t s) = f' s :=
    (show HasSum (fun t => g t s) (f' s) from by
      change HasSum (fun t => v s*K.premium (X.wrapY s.1) W o.a Q.table k Q.halo s.2 (issue Y k t))
        (K.salary (X.wrapY s.1) k W o.a Q.table Y s.2*v s)
      rw [mul_comm _ (v s)]
      exact (K.tons (X.wrapY s.1) k H width manifest Y layout s.2).mul_left (v s)).tsum_eq
  change HasSum (fun t=> ∫ s,g t s ∂D) (∫ s,f' s ∂D)
  rw [←funext whole]
  exact hx

include H in
theorem shore (hm : ∀ b∈J,Measurable (h b))
    (unit : ∀ b∈J,∀ e∈Set.Icc 0 (linkCap S),‖h b e‖≤1) :
    (∫ s,K.realP X s k W * X.sampled J h s ∂F.order G) =
    ∫ s,∫ u,K.realP X ((X.wrapY s).shifted u) k W *
      X.sampled J h ((X.wrapY s).shifted u) ∂X.stages ∂F.order G := by
  let f s := K.realP X s k W * X.sampled J h s
  have hf : Integrable f (F.order G) := mul_integrable ((K.world X H.laws.intake H.laws.data.W_pos).1 k)
    (X.sampled_measurable H J h hm) (sampled_unit X J h unit)
  have he : Integrable (f ∘ X.shore.symm) _ :=
    (X.propagation.symm.integrable_comp_emb X.shore.symm.measurableEmbedding).mpr hf
  let g v := ∫ z,f (X.shore.symm (z,v)) ∂X.stages
  have hr : Integrable (fun w : (X.Signal → G.El)×(X.Fog → G.El) => g w.2)
      (X.stages.prod X.forecast) := he.integral_prod_right.comp_snd _
  rw [←X.propagation.symm.integral_comp' f]
  symm
  change (∫ s,∫ z,f ((X.wrapY s).shifted z) ∂X.stages ∂_)=_
  rw [←X.propagation.symm.integral_comp' (fun s => ∫ z,f ((X.wrapY s).shifted z) ∂X.stages)]
  simp_rw [Coat.shifted]
  change (∫ v,∫ z,f (X.shore.symm (z,(X.shore (X.shore.symm v)).2)) ∂X.stages ∂_)=_
  simp_rw [X.shore.apply_symm_apply]
  rw [Function.comp_def] at he
  rw [integral_prod_symm _ hr,integral_prod_symm _ he]
  simp [g]

def hike (Y : Coat T F) (p : Molecule S) (w a : ℝ) (A : ChartRatio G) (l : ℕ) :=
  if Y.approve k R then ∫ s,raw (W:=w) K Y k p a A l J h s ∂((F.order G).prod Y.dice) else 0

include H width in
theorem troops (Y : Finset (Stores S)) (layout : Layout X.seeds Q.halo X.B Y)
    (hm : ∀ b∈J,Measurable (h b)) (unit : ∀ b∈J,∀ e∈Set.Icc 0 (linkCap S),‖h b e‖≤1) :
    HasSum (fun t => X.tribute R Q.table *
      hike K k J h X (issue Y k t) W o.a Q.table Q.halo)
      (∫ s,K.realP X s k W * X.sampled J h s ∂F.order G) := by
  by_cases ha : X.approve k R
  · simp_rw [hike,if_pos ha]
    obtain ⟨hi,hs⟩ := measured_series K X H width k J h ha.1 Y layout hm unit
    convert! hs.mul_left (X.tribute R Q.table) using 1
    rw [shore K X H k J h hm unit,integral_prod _ hi,←integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun s =>
      sector_chart K (X.wrapY s) H width k J h ha.1 Y layout ha.2.1 hm)
  have he s : K.realP X s k W=0 := by
    by_contra hn
    exact ha (K.exterior X k H.laws.intake H.laws.data.W_pos s hn)
  simp_rw [he,zero_mul,hike,if_neg ha,integral_zero,mul_zero]
  exact hasSum_zero

end YM.Integration.InletSusceptibility.JointTicket
