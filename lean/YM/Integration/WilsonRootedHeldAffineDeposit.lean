import YM.Integration.WilsonRootedHeldPacketGerm
import YM.Integration.WilsonRootedHeldAffineStation
import YM.Integration.WilsonRetainedSiteWickWord

/-! The earlier filed packet, with its own temperature, on the measured held
    forest. Only the angular center is replaced, at fixed compact exterior,
    old minimizing branch and unchanged common Gaussian and Haar variables. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedHeldAffineDeposit
open Lattice Wilson RG Tree Pressure Function MeasureTheory Matrix
open ConnectedActivityE6 Coat Control Window Census Blaze
open Push Push.AbsoluteSums Precision SectorMeasure Oriented
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open OriginalMarkedRunAction
open scoped Topology BigOperators Classical
variable {G:Gauge}{c f L:Side}{S:StepData c f}{T:Tube G S}{F:Forest S.ratio}{P:Teller G}
variable {W γ σ D:ℝ}

/-- Same full conditional normal equation and same original noise. -/
abbrev normalSample (X:Coat T F)(β:ℝ)(z:Air f G):Directions G f :=
  erect G (WilsonRootedHeldAffineCenter.full X)+gStep β • X.atmos z

def exchange (X:Coat T F)(a:PrismA G)(x:Site f)(β g ratio:ℝ)(w:F.Slice G×Air f G):ℝ:=
  let Y:=X.wrapY w.1
  siteWeight a g ratio*(sitePacket a.cells x (Y.input (Y.liftA β w.2))-
    sitePacket a.cells x (Y.input (normalSample Y β w.2)))

theorem measured (X:Coat T F)(shell:ShellAccess S G X.x W X.width γ)(funds:P.Funds S T)
    (a:PrismA G)(draw:Commission a.cells σ D a.grade)(hs:0<σ)(x:Site f)(β g ratio:ℝ):
    Measurable (exchange X a x β g ratio):=by
  let Ω:=F.Slice G×Air f G
  have active:=X.airwards (v:=fun z:Ω=>z.2) shell funds (Y:=fun z:Ω=>z.1) measurable_fst
  have full:Measurable (fun z:Ω=>WilsonRootedHeldAffineCenter.full (X.wrapY z.1)):=
    (show Continuous (fun v:Tubular f G→ℝ=> -((X.plate⁻¹).transpose *ᵥ v)) by fun_prop).measurable.comp active.1
  have mean:Measurable (fun z:Ω=>erect G (WilsonRootedHeldAffineCenter.full (X.wrapY z.1))):=by
    apply measurable_pi_lambda
    intro e
    let lin:(Tubular f G→ℝ)→ₗ[ℝ]G.Color :=
      {toFun := fun v=>erect G v e
       map_add' := fun _ _=>rfl
       map_smul' := fun _ _=>rfl}
    exact lin.continuous_of_finiteDimensional.measurable.comp full
  have noise:Measurable (fun z:Ω=>X.atmos z.2):=
    measurable_pi_lambda _ fun e=>(X.tale e).measurable.comp measurable_snd
  have normalM:Measurable (fun z:Ω=>normalSample (X.wrapY z.1) β z.2):=
    mean.add ((measurable_const (a:=gStep β)).smul noise)
  have scored:=(site_packet a.cells hs draw.toll x).1
  exact measurable_const.mul ((scored.comp (X.summon measurable_fst (active.2.2 β measurable_snd))).sub
    (scored.comp (X.summon measurable_fst normalM)))

theorem compared (X:Coat T F)(a:PrismA G)(draw:Commission a.cells σ D a.grade)(hs:0<σ)
    (x:Site f)(β g ratio:ℝ)(w:F.Slice G×Air f G):
    |exchange X a x β g ratio w|≤ |siteWeight a g ratio| *
      (D*WilsonRootedHeldPacketGerm.tariff G (a.rise+2) 1 σ)*
      ‖(X.wrapY w.1).μ-erect G (WilsonRootedHeldAffineCenter.full (X.wrapY w.1))‖:=by
  let Y:=X.wrapY w.1
  have h:=WilsonRootedHeldPacketGerm.compared Y a draw hs x (Y.liftA β w.2) (normalSample Y β w.2)
  rw [Coat.liftA,normalSample,add_sub_add_right_eq_sub] at h
  unfold exchange
  rw [abs_mul,mul_assoc]
  exact mul_le_mul_of_nonneg_left h (abs_nonneg _)

end YM.Integration.WilsonRootedHeldAffineDeposit
