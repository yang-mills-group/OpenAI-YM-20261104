import YM.Integration.WilsonPhysicalHistoryRetainedSpringBareRows

/-! Both low curvature entries of the old path use one and the same signed
coefficient, held field and Gaussian sampling. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure RGLocalTaylor
open Coat Matter Pond Blaze.March PhysicalNext.Repeat Greenbelt PhysicalNext.Repeat.Legato
open Dict06.Series RGLocalTaylor.Insert Work.F03 Bid Coat Matter
open AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open IterationFour.Vacuum Comparison.RG02 Comparison.RG02.Assembly
open scoped Topology BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {R : Rep G f}
variable {P : Teller G} {Q : ConnectedActivityE6.Target G P} {W s μ C : ℝ} {o : Target.Order G W}

def interactionTaylor (K : PathData G) (x : Site f) (z : Dir G f) (q : Bool→ℕ) (g : ℝ) : ℂ:=
  siteTaylor K.cubic x z (q false) g+siteTaylor K.quartic x z (q true) g

theorem chamber_interaction (H : Cash W s μ L Q o C T R) (temp : 0≤Pressure.temp s)
    (χ : Chi) (v : Finset (LocalLTE.Fan.Veil c f)) (i : Greenbelt.Reserve S) (tag : S.Choices)
    (y : (Greenbelt.allot i).Slice G) {K : PathData G} {B : Clip} {σ D Λ : ℝ}
    (paid : K.Bounds B σ D Λ) (x : Site f) (q : Bool→ℕ) (l : ℕ) (g w : ℝ) (hg : 0<g) :
    let X:=WilsonCoherentMayerHearing.chamber T s o.K χ 1 v i tag
    let F:=Greenbelt.allot i
    let E:=fun z : Air f G=>(w:ℂ)*((interactionAt K x ((X.wrapY y).input
      ((X.wrapY y).liftA (Integral.temperature g) z)):ℂ)-interactionTaylor K x (angularSample F z) q g)
    let fee:=fun b=>|w| *(D*(2*speedPrice G L o.eta o.gap o.ample ((q b+1)*(l+1)-1)*|g|/σ)^(q b+1))
    Integrable E X.dice ∧ Integrable (fun z=>‖E z‖^(l+1)) X.dice ∧
      (∫ z,‖E z‖^(l+1) ∂X.dice)≤(fee false+fee true)^(l+1) := by
  intro X F E fee
  let d:=fun b (z : Air f G)=>(w:ℂ)*((sitePacket (interactionRows K b) x
    ((X.wrapY y).input ((X.wrapY y).liftA (Integral.temperature g) z)):ℂ)-
    siteTaylor (interactionRows K b) x (angularSample F z) (q b) g)
  have filed (b : Bool) : Integrable (d b) X.dice ∧ Integrable (fun z=>‖d b z‖^(l+1)) X.dice ∧
      (∫ z,‖d b z‖^(l+1) ∂X.dice)≤(fee b)^(l+1):=
    chamber_bare_rows H temp χ v i tag y paid b x (q b) l g w hg
  have eq (z : Air f G) : E z=∑ b : Bool,d b z:=by
    simp only [E,d,interactionAt,interactionTaylor,Fintype.sum_bool,interactionRows,Complex.ofReal_add]
    exact (show ∀ (w u v p q : ℂ),w*((u+v)-(p+q))=w*(v-q)+w*(u-p) by intros; ring) _ _ _ _ _
  have captured : Integrable E X.dice:=by
    rw [funext eq]
    exact integrable_finsetSum _ fun b _=>(filed b).1
  have D0 : 0≤D:=(tsum_nonneg paid.three.1).trans paid.three.2.2
  have positive (b : Bool) : 0≤fee b:=by
    dsimp only [fee]
    have M:=(speed_price_pos G L o.eta o.gap o.ample ((q b+1)*(l+1)-1)).le
    positivity [paid.width]
  obtain ⟨whole,bound⟩:=pool_finite X.dice univ fee (fun b z=>‖d b z‖) (fun b _=>positive b)
    (fun b _ z=>norm_nonneg _) (fun b _=>(filed b).1.norm.aestronglyMeasurable) l (fun b _=>(filed b).2)
  have pointwise (z : Air f G) : ‖E z‖^(l+1)≤(∑ b : Bool,‖d b z‖)^(l+1):=by
    apply pow_le_pow_left₀ (norm_nonneg _)
    rw [eq]
    exact norm_sum_le _ _
  have result:=whole.mono' ((continuous_pow (l+1)).comp_aestronglyMeasurable captured.norm.aestronglyMeasurable)
    (ae_of_all _ fun z=>by rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]; exact pointwise z)
  refine ⟨captured,result,(integral_mono result whole pointwise).trans (bound.trans_eq ?_)⟩
  rw [Fintype.sum_bool,add_comm]

end YM.Integration.OriginalMarkedRunAction
