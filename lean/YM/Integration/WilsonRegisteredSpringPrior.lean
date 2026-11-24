import YM.Integration.WilsonRegisteredSpringWickLeaf
import YM.Integration.WilsonRetainedPriorCofactor

/-! The whole incoming spring and the entire original vacuum molecule in the
same signed numerator. The square-integrable polynomial may share all of the
moving coordinates with both operands. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open IterationFour IterationFour.Vacuum Comparison.RG02
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure RGLocalTaylor
open Coat Matter Pond Blaze.March PhysicalNext.Repeat Greenbelt PhysicalNext.Repeat.Legato Work.F03 Bid
open PhysicalNext.Repeat.Malachite AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open Next.SectorChange WilsonCoherentMayerProjection Next.Rank Comparison.RG02.Cumulants Comparison.RG02.Assembly
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoherentMayerHearing Dict06.Series
open Census Window
open scoped BigOperators Classical ENNReal
variable {G : Gauge} (R : Run G) {m N : ℕ} (per : ℕ)
local notation "S₀" => R.family.path.levels.clock.op m per
local notation "s₀" => R.family.path.levels.clock.hatBeta m
local notation "g₀" => Pert.Asymptotics.regulatorRun R.family N per (m+1)
local notation "f₀" => R.family.side (m+1) per
local notation "P₀" => R.family.path.rep N per (m+1)

theorem spring_prior (later : m+1<N) (d : ℕ) (A : Comparison R (p:=per) later d)
    (Z : SeriesA G) {σ C : ℝ} (hs : 0<σ) (filed : Draw Z σ C) (top : ℕ)
    (grade : ∀a∈Z,a.grade≤top) (r K : ℕ) {ε η : ℝ} (ep : 0≤ε)
    (sale : SpringSiteEstimate R m N Z r K 1 ε η)
    {W μ cost : ℝ} {M : Teller G} {D : ConnectedActivityE6.Target G M} {o : Target.Order G W}
    {T : Tube G S₀} (H : Cash W s₀ μ (S₀).patch.L D o cost T P₀)
    (temp : 0≤Pressure.temp s₀) (jump : WilsonCoherentMayerCovarianceCalendar.deviation G (S₀).patch.L o≤
      1+Real.log (betaF G s₀ (S₀).patch.L))
    (small : (Real.sqrt 2*Pert.Asymptotics.regulatorRun R.family N per (m+2))^(d+1)≤1)
    (quarter : ∀ {F : Forest (S₀).ratio} (X : Coat T F), X.x=s₀ → X.width=o.K → X.manifest →
      ∀ (y : F.Slice G) (l : Finset ℕ) (z : Air f₀ G) (i : ℕ),
        |(X.wrapY y).vertex P₀ D.table W o.a l D.halo z (regularHead S₀ i)|≤1/4) :
    ∃ b : ℕ→ℝ, (∀ x,SumBudget (fun i=>if ((P₀).activities.reg i).site=x then
      (P₀).p.mass ((P₀).activities.reg i).support (b i) else 0)
      ((Real.sqrt 2*Pert.Asymptotics.regulatorRun R.family N per (m+2))^(d+1))) ∧
    ∀ (χ : Chi) (fan : Finset (LocalLTE.Fan.Veil (R.family.side m per) f₀))
      (i : Greenbelt.Reserve S₀) (tag : (S₀).Choices) (x : Site f₀),
    let F:=Greenbelt.allot i
    let X:=chamber T s₀ o.K χ 1 fan i tag
    let ν:=(F.order G).prod X.dice
    let spr:=registeredSpring R N per (m+1) r Z X x K g₀
    ∀ (l : Finset ℕ) (p : Molecule S₀) (B : Normal.poly (Eye X)),
    let read:=fun (J : Normal.poly (Eye X)) (z : Air f₀ G)=>Cloud.paint (fun v=>z (tube X v)) J
    let left:=fun u : F.Slice G × Air f₀ G=>read B u.2*(springAt R N per (m+1) r Z g₀ x
      ((X.wrapY u.1).input ((X.wrapY u.1).liftA (Integral.temperature g₀) u.2)):ℂ)*
      (X.body P₀ D.table W o.a l D.halo p u:ℂ)
    let right:=fun u : F.Slice G × Air f₀ G=>read (B*spr) u.2*
      (X.body (approximation R (p:=per) later d) D.table W o.a l D.halo p u:ℂ)
    let wallet:=fun (J : Normal.poly (Eye X))=>Rise.coin J*
      (1+Real.sqrt (Common.priced (1+payE o.eta o.gap o.ample (tubularPrice G (S₀).patch.L))
        (2*(2*J.totalDegree))))
    let err:=fun v : Head S₀=>(5/2:ℝ)*regularFee S₀ b v
    let bill:=insertedCost (fun v=>H.fair v+err v) err p.toList
    Integrable left ν ∧ Integrable right ν ∧
    ‖(∫u,left u ∂ν)-∫u,right u ∂ν‖≤
      (wallet B*(ε*g₀^(((K+3:ℕ):ℝ)-η)))*(∏v∈p,H.fair v)+
      wallet (B*spr)*Real.sqrt (H.alarms^(blaze p).card)*bill := by
  obtain ⟨b,budget,charged⟩:=molecule_correlated R later A
  refine ⟨b,budget,?_⟩
  intro χ fan i tag x F X ν spr l p B read left right wallet err bill
  letI : IsProbabilityMeasure (F.order G) := by unfold Forest.order; infer_instance
  letI : SFinite (F.order G) := by unfold Forest.order; infer_instance
  have manifest : X.manifest := by
    change (roster (LocalLTE.Fan.arm (S:=S₀) fan)).flags=RG.flags (Pressure.temp s₀) (1:Config G _)
    rw [LocalLTE.Fan.Field.rosterD]
    exact (Greenbelt.prism T s₀ χ o.K (1:Config G _) F).bowed temp
  obtain ⟨rot,-,-,-⟩:=H.laws.data.localP F X rfl rfl manifest
  have gpos : 0<g₀:=IterationFour.Currency.g_pos R.makes N per (m+1) later.le
  let β:=Integral.temperature g₀
  have bp : 0<β:=by dsimp only [β,Integral.temperature]; positivity
  have path (y : F.Slice G) (z : Air f₀ G) :
      (X.wrapY y).input ((X.wrapY y).liftA β z)=represent (g₀ • angularSample F z) := by
    simpa only [β,inverse_temperature_step gpos,mul_inv_cancel₀ gpos.ne',one_smul] using
      chamber_path H.laws.data.funds.funds s₀ o.K χ i fan tag bp y z g₀
  let J:=B*spr
  let E:=fun z : Air f₀ G=>(springAt R N per (m+1) r Z g₀ x (represent (g₀ • angularSample F z)):ℂ)-read spr z
  let fee:=ε*g₀^(((K+3:ℕ):ℝ)-η)
  have fnn:0≤fee:=mul_nonneg ep (Real.rpow_nonneg gpos.le _)
  have paint (z : Air f₀ G) : read spr z=springTaylorAt R N per (m+1) r Z x (angularSample F z) K g₀ :=
    (registered_spring R N per (m+1) r later.le Z hs filed top grade X x K g₀).2.2 z
  let e1:=fun z : Air f₀ G=>(springAt R N per (m+1) r Z g₀ x
    ((X.wrapY 1).input ((X.wrapY 1).liftA β z)):ℂ)-springTaylorAt R N per (m+1) r Z x (angularSample F z) K g₀
  have same : e1=E := by
    funext z
    dsimp only [e1,E]
    rw [path 1 z,paint z]
  have single : Integrable E X.dice ∧ Integrable (fun z=>‖E z‖^2) X.dice ∧
      (∫z,‖E z‖^2 ∂X.dice)≤fee^2 := by
    rw [←same]
    exact sale per H temp jump χ fan i tag 1 x
  have b2:=mark_power X rot B 1
  have j2:=mark_power X rot J 1
  have cs:=WilsonCoherentMayerFuelCofactor.mixed X (read B) E b2.1 fnn b2.2.1
    single.1.aestronglyMeasurable b2.2.2.1 single.2.1 b2.2.2.2 single.2.2
  let gross:=∏v∈p,H.fair v
  let old:=X.body P₀ D.table W o.a l D.halo p
  let new:=X.body (approximation R (p:=per) later d) D.table W o.a l D.halo p
  let keep:=fun u : F.Slice G × Air f₀ G=>read J u.2*(old u:ℂ)
  let first:=fun u : F.Slice G × Air f₀ G=>(read B u.2*E u.2)*(old u:ℂ)
  let second:=fun u : F.Slice G × Air f₀ G=>read J u.2*((old u-new u:ℝ):ℂ)
  have gross0 : 0≤gross:=Finset.prod_nonneg fun v _=>H.fair_price v
  have paid (u) : |old u|≤gross := by
    change |∏v∈p,(X.wrapY u.1).vertex P₀ D.table W o.a l D.halo u.2 v|≤_
    rw [Finset.abs_prod]
    exact Finset.prod_le_prod (fun _ _=>abs_nonneg _) (fun v _=>H.voice (X.wrapY u.1) rfl rfl manifest l v u.2)
  have om: AEStronglyMeasurable (fun u=>(old u:ℂ)) ν :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable (H.integrated X rfl rfl manifest l p).aestronglyMeasurable
  have mp : MeasurePreserving (Prod.snd : F.Slice G × Air f₀ G→_) ν X.dice:=measurePreserving_snd (μ:=F.order G) (ν:=X.dice)
  have bM:=b2.2.1.comp_measurePreserving mp
  have eM:=single.1.aestronglyMeasurable.comp_measurePreserving mp
  have jM:=j2.2.1.comp_measurePreserving mp
  have major : Integrable (fun u : F.Slice G × Air f₀ G=>(‖read B u.2‖*‖E u.2‖)*gross) ν :=
    (mp.integrable_comp_of_integrable cs.1).mul_const gross
  have bound (u) : ‖first u‖≤(‖read B u.2‖*‖E u.2‖)*gross := by
    simp only [first,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (paid u) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have fi : Integrable first ν:=major.mono' ((bM.mul eM).mul om) (ae_of_all _ bound)
  have integral : (∫u,‖read B u.2‖*‖E u.2‖ ∂ν)=∫z,‖read B z‖*‖E z‖ ∂X.dice := by
    rw [integral_fun_snd (μ:=F.order G) (ν:=X.dice) (fun z=>‖read B z‖*‖E z‖)]
    simp [Measure.real]
  have firstPrice : ‖∫u,first u ∂ν‖≤(wallet B*fee)*gross := by
    apply (norm_integral_le_integral_norm _).trans ((integral_mono fi.norm major bound).trans ?_)
    rw [integral_mul_const,integral]
    exact mul_le_mul_of_nonneg_right cs.2 gross0
  have squares : (∫u,‖read J u.2‖^2 ∂ν)=∫z,‖read J z‖^2 ∂X.dice := by
    rw [integral_fun_snd (μ:=F.order G) (ν:=X.dice) (fun z=>‖read J z‖^2)]
    simp [Measure.real]
  have sq := mp.integrable_comp_of_integrable j2.2.2.1
  have s2 := charged H X rfl rfl manifest small (quarter X rfl rfl manifest) l p
    (fun u=>read J u.2) jM sq
  have unitPrice:= (charged H X rfl rfl manifest small (quarter X rfl rfl manifest) l p
    (fun _=>(1:ℂ)) aestronglyMeasurable_const (by simp)).2
  have bn : 0≤Real.sqrt (H.alarms^(blaze p).card)*bill := by
    exact (norm_nonneg _).trans (by simpa [ν] using unitPrice)
  have smallJ : Real.sqrt (∫u,‖read J u.2‖^2 ∂ν)≤wallet J := by
    rw [squares]
    exact (Real.sqrt_le_sqrt j2.2.2.2).trans_eq (Real.sqrt_sq j2.1)
  have secondPrice : ‖∫u,second u ∂ν‖≤wallet J*Real.sqrt (H.alarms^(blaze p).card)*bill :=
    s2.2.trans (by
      rw [mul_assoc,mul_assoc]
      exact mul_le_mul_of_nonneg_right smallJ bn)
  have jr : Integrable (fun u : F.Slice G × Air f₀ G=>read J u.2) ν :=
    mp.integrable_comp_of_integrable (WilsonCoherentMayerFuelSquare.sampled X rot.fullC J).1
  have ki : Integrable keep ν:= (jr.norm.mul_const gross).mono' (jM.mul om) (ae_of_all _ fun u=>by
    simp only [keep,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (paid u) (norm_nonneg _))
  have eqL : left=fun u=>keep u+first u := by
    funext u
    dsimp only [left,first,keep,old,E,J,read]
    rw [path u.1 u.2,map_mul]
    ring
  have eqR : right=fun u=>keep u-second u := by
    funext u
    dsimp only [right,keep,second,old,new,J]
    push_cast
    ring
  rw [eqL,eqR]
  refine ⟨ki.add fi,ki.sub s2.1,?_⟩
  rw [integral_add ki fi,integral_sub ki s2.1]
  have cancel (a b c : ℂ) : (a+b)-(a-c)=b+c := by ring
  rw [cancel]
  exact (norm_add_le _ _).trans (add_le_add firstPrice secondPrice)

end YM.Integration.OriginalMarkedRunAction
