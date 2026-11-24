import YM.Integration.WilsonCoherentMayerProjection
import YM.Integration.WilsonCoherentMayerMultiplier

/-! The full signed marked hearing at the held identity. Integrating out
the original gauge orbit leaves its conditional Mayer multiplier at the
very same Gaussian sample used to evaluate the finite Wilson source. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCoherentMayerGaussian
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure RGLocalTaylor
open Coat Matter Pond Blaze.March PhysicalNext.Repeat Greenbelt PhysicalNext.Repeat.Legato
open Dict06.Series RGLocalTaylor.Insert AnalyticBridge.LocalGaussianLaws
open WilsonCoherentMayerHearing
open scoped Topology BigOperators Classical
variable {G:Gauge} {c f L:Side} {S:StepData c f} {T:Tube G S}
variable {P:Teller G} {Q:ConnectedActivityE6.Target G P} {W s μ C:ℝ} {o:Target.Order G W}
  {R:Rep G f} (H:Cash W s μ L Q o C T R)
variable (run:Run G) {I:Type} [Fintype I] (d:I→ℕ) (θ:ℝ) (y:∀i,run.family.label (d i)) (loc:I→Site f)
variable {j n l k M:ℕ} {χ:Chi} {q r a b D v' Y C' A B price k' θ' wJ zJ:ℝ}

theorem original (v:Finset (LocalLTE.Fan.Veil c f)) {select:Molecule S}
    (u:Mayer.Decors select M) (hs:select⊆LocalLTE.Fan.arm (S:=S) v) (hw:Mayer.decorOrder u≤M)
    (N:Captain H j C' D v' Y A b r B q n χ)
    (law:Awning H N.conduit A b price a wJ zJ k l)
    (room:Q.goal L s≤k') (allow:Mayer.Approved k' θ' j M) (f':Head S→Insert T)
    (billed:∀ i∈LocalLTE.Fan.arm (S:=S) v\select,Fits H (f' i) (H.supportP i) j)
    (cohort:Mayer.Start select) (temp:0≤Pressure.temp s) {β:ℝ} (positive:0<β)
    (e:ℕ) (phase:ℂ→L[ℝ]ℝ) :
    hearing T s o.K χ 1 v (fun X z=>
      (Mayer.tagged H (LocalLTE.Fan.arm v) f' u).joint X z *
      phase (ordinary e (WilsonCoherentMayerField.marked run d θ y loc X β z))) =
    likely (fun i:Greenbelt.Reserve S=>likely (fun tag:S.Choices=>
      let F:=Greenbelt.allot i
      let X:= chamber T s o.K χ 1 v i tag
      ∫ z:Air f G, (∫ a:F.Slice G,Mayer.planned H (LocalLTE.Fan.arm v) u f' X (a,z) ∂F.order G) *
        phase (Tensor.diagonal (Tensor.coeff (WilsonCoherentMayerProjection.content run d θ y) e 0)
          (WilsonCoherentMayerProjection.restrict run d F loc z)) ∂X.dice)) :=by
  rw [WilsonCoherentMayerHearing.original H run d θ y loc v u hs hw N law room allow f' cohort temp β e phase]
  unfold hearing
  congr 1
  funext i
  congr 1
  funext tag
  dsimp only
  let F:=Greenbelt.allot i
  let X:=chamber T s o.K χ 1 v i tag
  let book (z:Air f G):=phase (PowerSeries.coeff e (WilsonCoherentMayerProjection.books run d F loc θ y z))
  let mul:=Mayer.planned H (LocalLTE.Fan.arm v) u f' X
  have present:X.manifest:=by
    change (roster (LocalLTE.Fan.arm (S:=S) v)).flags=RG.flags (Pressure.temp s) (1:Config G c)
    rw [LocalLTE.Fan.Field.rosterD]
    exact (Greenbelt.prism T s χ o.K (1:Config G c) F).bowed temp
  have healthy:Healthy (Pressure.temp s) (H.unionP (LocalLTE.Fan.arm v)) X.V:=by
    change Disjoint _ (RG.flags (Pressure.temp X.x) X.V)
    rw [←present]
    change Disjoint _ (roster (LocalLTE.Fan.arm (S:=S) v)).flags
    rw [LocalLTE.Fan.Field.rosterD]; exact Finset.disjoint_empty_right _
  have booked (z:momentSpace X):phase (PowerSeries.coeff e (issued run d θ y loc X β z))=book z.2:=by
    have clear:Assembly.Clear S (X.wrapY z.1).x (X.wrapY z.1).seeds F:=by
      change Assembly.Clear S s (roster (LocalLTE.Fan.arm (S:=S) v)) F
      rw [LocalLTE.Fan.Field.rosterD]
      exact Assembly.bare_is_Clear S s F
    unfold issued book WilsonCoherentMayerProjection.books
    rw [WilsonCoherentMayerNoise.drawn H.laws.data.funds.funds (X.wrapY z.1) rfl clear positive z.2]
  obtain ⟨hm,J,-,hJ⟩:=WilsonCoherentMayerMultiplier.earned u hs hw N law room allow f' billed cohort
      X healthy rfl rfl rfl present
  have hbook:Integrable book X.dice :=
    WilsonCoherentMayerProjection.integrable run d F loc θ y X e phase
  have joint:Integrable (fun z:momentSpace X=>mul z*book z.2) (moment X):=by
    have hc:=hbook.comp_snd (F.order G)
    apply (hc.norm.const_mul J).mono' (hm.aestronglyMeasurable.mul hc.aestronglyMeasurable)
    filter_upwards with z
    change ‖mul z*book z.2‖≤J*‖book z.2‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hJ z) (norm_nonneg _)
  change (∫z:momentSpace X,mul z*phase (PowerSeries.coeff e (issued run d θ y loc X β z)) ∂moment X)=_
  simp_rw [booked]
  have swap:=integral_prod_symm (μ:=F.order G) (ν:=X.dice) (fun z:momentSpace X=>mul z*book z.2) joint
  refine swap.trans ?_
  apply integral_congr_ae
  filter_upwards with z
  rw [integral_mul_const]
  exact congrArg ((∫a:F.Slice G,mul (a,z) ∂F.order G)* ·)
    (congrArg phase (WilsonCoherentMayerProjection.graded run d F loc θ y e z))

end YM.Integration.WilsonCoherentMayerGaussian
