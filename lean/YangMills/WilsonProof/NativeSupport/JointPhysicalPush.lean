import YangMills.WilsonProof.NativeSupport.JointSectorKernel

/-! Fixed-tag physical kernel and exact measured sector decomposition. No spatial
partition masses occur as denominators. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.BetaTransport Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations
open SectorMeasure Oriented Work.E03 Mask Contract Work.F03 Presented LabelSum Sector Footprint
open Packets SliceRows Control Window Pulse Coat Matter PhysicalNext.Repeat PhysicalNext.Repeat.Lotus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P : Teller G} {T : Tube G S}
    {F : Forest S.ratio} {R : Rep G f} {W μ C : ℝ}
    {Q : ConnectedActivityE6.Target G P} {o : ConnectedActivityE6.Target.Order G W}

namespace JointPhysical
variable (S) (k : S.Choices) (J : Finset (Bond c)) (h : Bond c→ℝ→ℝ)
def sample (U : Config G f) (V : Config G c) :=
  ∏ b∈J,h b (linkEnergy S (V b*(S.prediction U k b)⁻¹))

theorem sample_env {α : Type*} [MeasurableSpace α] {U : α → Config G f} {V : α → Config G c}
    (ok : S.patch.Branches S.kernel G) (hU : Measurable U) (hV : Measurable V)
    (hm : ∀ b∈J,Measurable (h b)) (unit : ∀ b∈J,∀ e∈Set.Icc 0 (linkCap S),‖h b e‖≤1) :
    Envelope (fun a => sample S k J h (U a) (V a)) := by
  refine ⟨Finset.measurable_fun_prod J (fun b bJ=> ?_),1,fun a=> ?_⟩
  · apply (hm b bJ).comp
    apply (link_estimate S).measurable.comp
    exact ((measurable_pi_apply b).comp hV).mul
      (((measurable_pi_apply b).comp ((S.prediction_meas ok k).comp hU)).inv)
  unfold sample
  rw [norm_prod]
  exact Finset.prod_le_one (fun _ _=> norm_nonneg _) fun b bJ=>
    unit b bJ _ ⟨(link_estimate S).nonneg _,(link_estimate S).bound _⟩

private theorem predict (ok : S.patch.Branches S.kernel G) (z : Site f→G.El) (U : Config G f) :
    S.prediction (Lattice.gauge z U) k=Lattice.gauge (z ∘ S.ratio.embed) (S.prediction U k) := by
  funext b
  unfold StepData.prediction
  rw [S.updateGauged ok,(S.patch.bond_gauge (h:=ok) ..).2]
  rfl

private theorem conjugate (z : Site c→G.El) (U V : Config G c) (b : Bond c) :
    (Lattice.gauge z V) b *((Lattice.gauge z U) b)⁻¹ =
      z b.1*(V b*(U b)⁻¹)*(z b.1)⁻¹ := by
  unfold Lattice.gauge
  group

theorem gauge (ok : S.patch.Branches S.kernel G) (z : Site f→G.El) (U : Config G f) (V : Config G c) :
    sample S k J h (Lattice.gauge z U) (Lattice.gauge (z ∘ S.ratio.embed) V)=sample S k J h U V := by
  unfold sample
  rw [predict S k ok]
  apply prod_congr rfl
  intro b _
  rw [conjugate,linkEnergy,G.price_conj]
  rfl

theorem tagged_gauge (β : ℝ) (ok : S.patch.Branches S.kernel G) (z : Site f→G.El)
    (U : Config G f) (V : Config G c) :
    taggedKernel S β k (Lattice.gauge z U) (Lattice.gauge (z ∘ S.ratio.embed) V)=taggedKernel S β k U V := by
  have hl : S.likelihood (Lattice.gauge z U) k=S.likelihood U k := by
    unfold StepData.likelihood
    apply congr_arg₂
    · refine Finset.prod_congr rfl fun j _ => ?_
      rw [expandAt_gauge]
      exact (S.patch.frame_gauged ok ..).1
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [S.updateGauged ok]
    exact (S.patch.bond_gauge (h:=ok) ..).1
  unfold taggedKernel
  rw [hl,predict S k ok]
  apply congr_arg
  unfold StepData.noise
  apply prod_congr rfl
  intro b _
  rw [conjugate,StepData.penaltyWeight,G.price_conj]
  rfl

def integrand (β : ℝ) (g : Config G f→ℝ) (V : Config G c) (U : Config G f) :=
  (taggedKernel S β k U V * g U)*sample S k J h U V

def push (β : ℝ) (g : Config G f→ℝ) (V : Config G c) :=
  ∑ k,∫ U,integrand S k J h β g V U ∂prior G f

theorem pack (F : Forest S.ratio) (β : ℝ) {g : Config G f→ℝ} (V : Config G c)
    (ok : S.patch.Branches S.kernel G) (hg : Envelope g) (sym : GaugeInvariant g)
    (hm : ∀ b∈J,Measurable (h b)) (unit : ∀ b∈J,∀ e∈Set.Icc 0 (linkCap S),‖h b e‖≤1) :
    (∫ U,integrand S k J h β g V U ∂prior G f) =
      ∫ a,integrand S k J h β g V (F.drape a) ∂F.order G := by
  have e : Envelope (integrand S k J h β g V) :=
    ((env_tagged β k ok measurable_id measurable_const).mul hg).mul
      (sample_env S k J h ok measurable_id measurable_const hm unit)
  apply F.pack _ (e.integrable _)
  intro z hz U
  have fixed : Lattice.gauge (z ∘ S.ratio.embed) V=V := by funext; simp [Lattice.gauge,hz]
  unfold integrand
  rw [←fixed,tagged_gauge S k β ok,gauge S k J h ok,sym]
  rw [fixed]

end JointPhysical

namespace JointTicket
variable (K : Team R) (X : Coat T F) (H : Cash W X.x μ L Q o C T R)
variable (J : Finset (Bond c)) (h : Bond c→ℝ→ℝ)

include H in
theorem world (hm : ∀ b∈J,Measurable (h b)) (unit : ∀ b∈J,∀ e∈Set.Icc 0 (linkCap S),‖h b e‖≤1) :
    HasSum (fun k => ∫ s,K.realP X s k W * X.sampled J h s ∂F.order G)
      (∫ s,(X.χ.distribute X.seeds X.x W (F.drape s) X.k X.V *
        (taggedKernel S R.beta X.k (F.drape s) X.V*K.cicada (F.drape s))) *
        X.sampled J h s ∂F.order G) := by
  obtain ⟨⟨b,hb,bound⟩,meas⟩ := K.escorts X H.laws.intake H.laws.data.W_pos
  let f k s := K.realP X s k W * X.sampled J h s
  have env k : Envelope (f k) := ⟨(meas k).mul (X.sampled_measurable H J h hm), b k,
    fun s=> (norm_mul _ _).trans_le ((mul_le_of_le_one_right (norm_nonneg _) (sampled_unit X J h unit s)).trans (bound k s))⟩
  have ing k : Integrable (f k) (F.order G) := (env k).integrable _
  have cost k s : ‖f k s‖≤b k := (norm_mul _ _).trans_le
    ((mul_le_of_le_one_right (norm_nonneg _) (sampled_unit X J h unit s)).trans (bound k s))
  have sum : Summable (fun k => ∫ s,‖f k s‖ ∂F.order G) :=
    hb.of_nonneg_of_le (fun _=> integral_nonneg fun _=>norm_nonneg _) fun k => by
      simpa using integral_mono (ing k).norm (integrable_const (b k)) (g:=fun _=>b k) (cost k)
  have hs := hasSum_integral_of_summable_integral_norm ing sum
  have whole s := ((K.duel (W:=W) X H.laws.intake s).mul_right (X.sampled J h s)).tsum_eq
  change HasSum (fun k=>∫ s,f k s ∂F.order G) _
  convert! hs using 1
  exact integral_congr_ae (ae_of_all _ fun s => (whole s).symm)

include H in
theorem posted (hm : ∀ b∈J,Measurable (h b)) (unit : ∀ b∈J,∀ e∈Set.Icc 0 (linkCap S),‖h b e‖≤1) :
    JointPhysical.push S J h R.beta K.cicada X.V = ∑ l : Stores S,∑ k : S.Choices,
      ∫ a,(X.χ.distribute l X.x W (F.drape a) k X.V *
        (taggedKernel S R.beta k (F.drape a) X.V * K.cicada (F.drape a))) *
        JointPhysical.sample S k J h (F.drape a) X.V ∂F.order G := by
  let D := X.χ.profiles G S X.x W H.laws.data.W_pos (show 0<X.t by
    unfold Coat.t Pressure.fiery Pressure.temp
    have ht := zero_lt_one.trans H.laws.intake.height
    positivity)
  let g (k : S.Choices) (a : F.Slice G) := JointPhysical.integrand S k J h R.beta K.cicada X.V (F.drape a)
  obtain ⟨hg,gs⟩ := K.sells H.laws.intake.cap
  let ok := funds_branch H.laws.intake.ready
  have gi k : Integrable (g k) (F.order G) := ((env_tagged R.beta k ok F.continuous_drape.measurable
    measurable_const |>.mul (Env.along hg F.continuous_drape.measurable)).mul (JointPhysical.sample_env S k J h
      ok F.continuous_drape.measurable measurable_const hm unit)).integrable _
  calc
    _ = tagTotal F g := sum_congr rfl fun k _ => JointPhysical.pack S k J h F R.beta X.V ok hg gs hm unit
    _ = ∑ l,D.column l F X.V g := (D.partitions ok F X.V g gi).symm
    _ = _ := by
      apply sum_congr rfl
      intro l _
      apply sum_congr rfl
      intro k _
      apply integral_congr_ae
      filter_upwards with a
      change X.χ.distribute l X.x W (F.drape a) k X.V *
        ((taggedKernel S R.beta k (F.drape a) X.V * K.cicada (F.drape a)) *
        JointPhysical.sample S k J h (F.drape a) X.V)=_
      ring

end JointTicket
end YM.Integration.InletSusceptibility
