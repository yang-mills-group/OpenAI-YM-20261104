import YM.Integration.ActualWilsonAbsoluteTransport
import YM.Integration.WilsonPurchasedRankWindow
import YM.MergeProof.Pitch

/-! All high-rank packet terms on a genuine Wilson window are paid at the two original physical endpoints. The remaining low response transports the exact original coherent subseries. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualWilsonThermalEndpoints
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Marker OPE.Therm OPE.Therm.House
open Comparison.Density.RenderM LocalComparison LocalComparison.MarkedPackets Push.AbsoluteSums
open WilsonThermalPacketSum WilsonThermalReadout WilsonPolynomialResponse
open scoped Classical BigOperators Topology Matrix.Norms.Frobenius
variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {R : Census V}
section Packet
variable {n : Side} {D : V → ComparisonDensity.Address.Orbit} {P : MarkedPackets D G n R} {q : BudgetPoint}
  {address : V→Support n} {region : Comparison.Density.Testing.Region (fun v => (D v).Mood) n}
  {w : V→ℝ} {g width budget : ℝ} {o d : ℕ}
  (H : P.Paid q address region w g width budget o d) (x : IndependentTests D)
  (c cap : ℕ) (hcap : P.rankCap≤cap)

include H hcap in
theorem model (L : Poly R →L[ℂ] ℂ) (hL : ∀ a,‖L a‖≤Poly.price w a) :
    Envelope (fun U => L (Poly.pass (P.read (testInclusion D x) g U))) := by
  have h : Measurable (fun U => P.read (testInclusion D x) g U) :=
    Measurable.tsum (fun i => (WilsonThermalReadout.atom P g x i).measurable)
  refine ⟨L.continuous.measurable.comp (Poly.pass_cont.measurable.comp h),Real.exp (uniformReadCost cap (Fintype.card V) budget),fun U => ?_⟩
  exact (hL _).trans ((Poly.pass_budget H.positive _).trans (Real.exp_le_exp.mpr (H.uniform_read cap hcap x U).2))

include H hcap in
theorem finite (L : Poly R →L[ℂ] ℂ) (hL : ∀ a,‖L a‖≤Poly.price w a) :
    Envelope (fun U => L (Poly.pass (low P g x c U))) := by
  have hm := model H x cap hcap L hL
  have hd := WilsonPairedRankCutoff.envelope H x c cap hcap L hL
  obtain ⟨M,hM⟩ := hm.cost
  obtain ⟨E,hE⟩ := hd.cost
  have eqn (U) : L (Poly.pass (low P g x c U)) =
      L (Poly.pass (P.read (testInclusion D x) g U))-L (gap P g x c U) := by rw [gap,map_sub];abel
  refine ⟨?_,M+E,fun U => ?_⟩
  · rw [funext eqn]
    exact hm.meas.sub hd.meas
  · rw [eqn U]
    exact (norm_sub_le ..).trans (add_le_add (hM U) (hE U))

include H hcap in
/-- Only matching original packet rows occur on a singleton in the full nonlinear low multiplier. -/
theorem singleton (v : V) (U : Config G n) :
    (Poly.pass (low P g x c U)).part (R.fire v)=∑' i, if P.rank i<c ∧ P.mode i=R.fire v
      then P.term (testInclusion D x) g U i else 0 := by
  let Q := WilsonPrescribedPacketTail.slice P (fun i => P.rank i<c)
  have hq : low P g x c U=Q.read (testInclusion D x) g U := by
    rw [low_eq x H c cap hcap U]
    unfold MarkedPackets.read
    apply tsum_congr
    intro i
    by_cases hi : P.rank i<c
    · cases hp : P.packet i <;> simp [Q,WilsonPrescribedPacketTail.slice,MarkedPackets.term,hi,hp]
    · simp [Q,WilsonPrescribedPacketTail.slice,MarkedPackets.term,hi]
  have zero : (low P g x c U).part R.quiet=0 := by rw [hq];exact Q.quiet_read _ _ U
  have hs := (H.uniform_read cap hcap x U).1.indicator {i | P.rank i<c}
  have h : Summable (fun i => if P.rank i<c then Poly.send (P.mode i) (P.term (testInclusion D x) g U i) else 0) := by
    apply hs.congr
    intro i
    by_cases h : P.rank i<c <;> simp [Set.indicator,h]
  rw [MergeProof.Accent.whisper R _ zero v,low_eq x H c cap hcap U,Poly.share h]
  apply tsum_congr
  intro i
  by_cases hi : P.rank i<c <;> by_cases hm : P.mode i=R.fire v <;>
    simp [hi,hm,eq_comm (a:=R.fire v)]

include H hcap in
theorem endpoint (μ : Measure (Config G n)) [IsProbabilityMeasure μ]
    (t δ : ℝ) (ht : 0≤t) (hd : 0≤δ) (rare : ∀ z : Face (Per n), μ.real (trigger z t)≤δ) :
    let price := fun U => Poly.price w (gap P g x c U)
    let bill := amplifier c cap (Fintype.card V) budget*cost c cap (Fintype.card V) t δ budget
    Integrable price μ ∧ (∫ U,price U ∂μ)≤bill ∧
    ∀ (L : Poly R →L[ℂ] ℂ), (∀ a,‖L a‖≤Poly.price w a)→
      (∫ U,‖L (gap P g x c U)‖ ∂μ)≤bill := by
  intro p bill
  let K := amplifier c cap (Fintype.card V) budget
  have h0 := (Poly.nonnegative H.positive _).trans (H.uniform_read cap hcap x (1:Config G n)).2
  have hK : 0≤K := WilsonThermalMultiplier.slope_nonneg _
    (add_nonneg h0 (budget_nonneg (at_field x H c cap hcap (1:Config G n))))
  have quota U : p U≤K*∑' i,entry P w g x c i U := field x H c cap hcap U
  refine ⟨Integrable.of_bound ((Poly.price_cont w).measurable.comp (WilsonThermalReadout.measurable P g x c)).aestronglyMeasurable
    (K*cost c cap (Fintype.card V) 2 0 budget) (ae_of_all _ fun U => ?_),?_,?_⟩
  · rw [Real.norm_of_nonneg (Poly.nonnegative H.positive _)]
    exact (quota U).trans (mul_le_mul_of_nonneg_left (at_field x H c cap hcap U).2.2 hK)
  · exact dominated x H μ c cap hcap t δ ht hd rare p K hK (fun U => Poly.nonnegative H.positive _) quota
  · intro L hL
    exact dominated x H μ c cap hcap t δ ht hd rare _ K hK (fun U => norm_nonneg _) (fun U => (hL _).trans (quota U))
end Packet

private theorem normSub {X : Type*} [MeasurableSpace X] {μ : Measure X} {f g : X→ℂ} (hf : Integrable f μ) (hg : Integrable g μ) :
    (∫ U,‖f U-g U‖ ∂μ)≤(∫ U,‖f U‖ ∂μ)+∫ U,‖g U‖ ∂μ := by
  rw [←integral_add hf.norm hg.norm]
  exact integral_mono (hf.sub hg).norm (hf.norm.add hg.norm) fun U => norm_sub_le _ _

theorem difference {C : Family G} (hC : C.Makes) {N p m j : ℕ} (hj : j≤N) (hm : m≤j)
    {f g : Config G (C.side j p)→ℂ} {u v : Config G (C.side m p)→ℂ}
    (hf : Integrable (fun T => (C.path.rep N p j).eval T • f T) (prior G _))
    (hg : Integrable (fun T => (C.path.rep N p j).eval T • g T) (prior G _))
    (hu : Integrable (fun U => u U-v U) (scene C.path N p m)) :
    (∫ U,‖(actualTransport C (N:=N) f hm U-u U)-(actualTransport C (N:=N) g hm U-v U)‖ ∂scene C.path N p m)≤
      (∫ T,‖f T-g T‖ ∂scene C.path N p j)+∫ U,‖u U-v U‖ ∂scene C.path N p m := by
  have hd : Integrable (fun T => (C.path.rep N p j).eval T • (f T-g T)) (prior G _) := by
    apply (hf.sub hg).congr
    exact ae_of_all _ fun T => (smul_sub ((C.path.rep N p j).eval T) (f T) (g T)).symm
  have ht := actualScene_integrable_of_weighted C hC (hm.trans hj) (actualTransport_weighted_integrable_of_integrable C hC hj hd hm)
  calc
    _ = ∫ U,‖actualTransport C (N:=N) (fun T => f T-g T) hm U-(u U-v U)‖ ∂scene C.path N p m := by
      apply integral_congr_ae (ae_of_all _ fun U => ?_)
      rw [ActualWilsonAbsoluteTransport.sub C hC hj hf hg hm]
      congr 1
      ring
    _ ≤ _ := normSub ht hu
    _ ≤ _ := add_le_add (ActualWilsonAbsoluteTransport.first C hC hj hd hm) le_rfl

section Window
variable {C : Family G} {N p m j : ℕ} {DF DC : V → ComparisonDensity.Address.Orbit}
local notation "mf" => C.side j p
local notation "mc" => C.side m p
variable {Pf : MarkedPackets DF G (C.side j p) R} {Pc : MarkedPackets DC G (C.side m p) R}
    {qf qc : BudgetPoint} {af : V→Support (C.side j p)} {ac : V→Support (C.side m p)}
    {rf : Comparison.Density.Testing.Region (fun v => (DF v).Mood) (C.side j p)}
    {rc : Comparison.Density.Testing.Region (fun v => (DC v).Mood) (C.side m p)}
    {wf wc : V→ℝ} {gf gc widthF widthC budgetF budgetC : ℝ} {ofF slF ofC slC : ℕ}
    (hf : Pf.Paid qf af rf wf gf widthF budgetF ofF slF)
    (hc : Pc.Paid qc ac rc wc gc widthC budgetC ofC slC)
    (xf : IndependentTests DF) (xc : IndependentTests DC)
local notation "μf" => scene C.path N p j
local notation "μc" => scene C.path N p m

include hf hc in
theorem window (_hC : C.Makes) (_hj : j≤N) (hm : m≤j) (c capF capC : ℕ)
    (_hF : Pf.rankCap≤capF) (_hK : Pc.rankCap≤capC)
    (tf δf tc δc : ℝ) (_htf : 0≤tf) (_hdf : 0≤δf) (_htc : 0≤tc) (_hdc : 0≤δc)
    (_rareF : ∀ z : Face (Per mf), (μf).real (trigger z tf)≤δf)
    (_rareC : ∀ z : Face (Per mc), (μc).real (trigger z tc)≤δc)
    (L : Poly R →L[ℂ] ℂ) (_lf : ∀ a,‖L a‖≤Poly.price wf a) (_lc : ∀ a,‖L a‖≤Poly.price wc a) :
    let fullF T := L (Poly.pass (Pf.read (testInclusion DF xf) gf T))
    let fullC U := L (Poly.pass (Pc.read (testInclusion DC xc) gc U))
    let lowF T := L (Poly.pass (low Pf gf xf c T))
    let lowC U := L (Poly.pass (low Pc gc xc c U))
    (∫ U,‖(actualTransport C (N:=N) fullF hm U-fullC U)-(actualTransport C (N:=N) lowF hm U-lowC U)‖ ∂μc)≤
      amplifier c capF (Fintype.card V) budgetF*cost c capF (Fintype.card V) tf δf budgetF+
        amplifier c capC (Fintype.card V) budgetC*cost c capC (Fintype.card V) tc δc budgetC :=
  let fullF T := L (Poly.pass (Pf.read (testInclusion DF xf) gf T))
  let fullC U := L (Poly.pass (Pc.read (testInclusion DC xc) gc U))
  let lowF T := L (Poly.pass (low Pf gf xf c T))
  let lowC U := L (Poly.pass (low Pc gc xc c U))
  letI : IsProbabilityMeasure μf := probability (H := C.path) (p := p) _hC.wilson _hj
  letI : IsProbabilityMeasure μc := probability (H := C.path) (p := p) _hC.wilson (hm.trans _hj)
  have ef (T) : fullF T - lowF T = L (gap Pf gf xf c T) := (map_sub L _ _).symm
  have ec (U) : fullC U - lowC U = L (gap Pc gc xc c U) := (map_sub L _ _).symm
  have hu : Integrable (fun U => fullC U - lowC U) μc :=
    by
      rw [show (fun U => fullC U - lowC U) = (fun U => L (gap Pc gc xc c U)) from funext ec]
      have envelope := WilsonPairedRankCutoff.envelope hc xc c capC _hK L _lc
      obtain ⟨bound, hbound⟩ := envelope.cost
      exact Integrable.of_bound envelope.meas.aestronglyMeasurable bound (ae_of_all μc hbound)
  (difference _hC _hj hm (ActualWilsonAbsoluteTransport.weighted C _hC _hj (model hf xf capF _hF L _lf))
    (ActualWilsonAbsoluteTransport.weighted C _hC _hj (finite hf xf c capF _hF L _lf)) hu).trans
    (add_le_add
      ((integral_congr_ae (ae_of_all μf fun T => congrArg norm (ef T))).le.trans
        ((endpoint hf xf c capF _hF μf tf δf _htf _hdf _rareF).2.2 L _lf))
      ((integral_congr_ae (ae_of_all μc fun U => congrArg norm (ec U))).le.trans
        ((endpoint hc xc c capC _hK μc tc δc _htc _hdc _rareC).2.2 L _lc)))

include hf hc in
theorem unit (_hC : C.Makes) (_hG : G.Simple) (_hj : j≤N) (hm : m≤j) (capF capC : ℕ)
    (_hF : Pf.rankCap≤capF) (_hK : Pc.rankCap≤capC)
    (tf δf tc δc : ℝ) (_htf : 0≤tf) (_hdf : 0≤δf) (_htc : 0≤tc) (_hdc : 0≤δc)
    (_rareF : ∀ z : Face (Per mf), (μf).real (trigger z tf)≤δf)
    (_rareC : ∀ z : Face (Per mc), (μc).real (trigger z tc)≤δc)
    (L : Poly R →L[ℂ] ℂ) (_lf : ∀ a,‖L a‖≤Poly.price wf a) (_lc : ∀ a,‖L a‖≤Poly.price wc a) :
    let fullF T := L (Poly.pass (Pf.read (testInclusion DF xf) gf T))
    let fullC U := L (Poly.pass (Pc.read (testInclusion DC xc) gc U))
    (∫ U,‖(actualTransport C (N:=N) fullF hm U-fullC U)-(fullF 1-fullC 1)‖ ∂μc)≤
      amplifier 2 capF (Fintype.card V) budgetF*cost 2 capF (Fintype.card V) tf δf budgetF+
        amplifier 2 capC (Fintype.card V) budgetC*cost 2 capC (Fintype.card V) tc δc budgetC :=
  let fullF T := L (Poly.pass (Pf.read (testInclusion DF xf) gf T))
  let fullC U := L (Poly.pass (Pc.read (testInclusion DC xc) gc U))
  let lowF T := L (Poly.pass (low Pf gf xf 2 T))
  let lowC U := L (Poly.pass (low Pc gc xc 2 U))
  have hf0 : lowF = (fun _ => fullF 1) :=
    funext fun T => congrArg (fun a => L (Poly.pass a)) (WilsonFlatPacketSource.subseries hf xf _hG capF _hF T)
  have hc0 (U) : lowC U = fullC 1 :=
    congrArg (fun a => L (Poly.pass a)) (WilsonFlatPacketSource.subseries hc xc _hG capC _hK U)
  have ho (U) : actualTransport C (N := N) lowF hm U = fullF 1 :=
    (congrArg (fun f => actualTransport C (N := N) f hm U) hf0).trans
      (actualTransport_const C _hC _hj (fullF 1) hm U)
  have h := window hf hc xf xc _hC _hj hm 2 capF capC _hF _hK tf δf tc δc
    _htf _hdf _htc _hdc _rareF _rareC L _lf _lc
  (integral_congr_ae (ae_of_all μc fun U =>
    congrArg (fun z => ‖(actualTransport C (N := N) fullF hm U - fullC U) - z‖)
      (congrArg₂ ((· - ·) : ℂ → ℂ → ℂ) (ho U).symm (hc0 U).symm))).le.trans h

end Window
end YM.Integration.ActualWilsonThermalEndpoints
end
