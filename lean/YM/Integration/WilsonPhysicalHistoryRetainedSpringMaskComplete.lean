import YM.Integration.WilsonPhysicalHistoryRetainedSpringMaskQuadratic
import YM.Integration.WilsonPhysicalHistoryRetainedSpringMaskRoster
import YM.Integration.WilsonPhysicalHistoryRetainedSpringIncoming

/-! Full signed independent earlier action in the actual physical law. Each
summand is masked on the genuine support registered with that very summand. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalMarkedRunAction
open Comparison.RG02 Function Filter Finset Lattice RG Wilson MeasureTheory OPE.Therm
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open IterationFour IterationFour.Vacuum PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open scoped Classical Topology BigOperators
variable {G : Gauge}

def maskedSpringAt (R : Run G) (N per j r : ℕ) (Z : SeriesA G) (σ C g : ℝ)
    (x : Site (R.family.side j per)) (U : Config G (R.family.side j per)) : ℝ :=
  let P:=R.family.path.rep N per j
  let B:=(R.family.path.levels.params j).clip
  let p:=finitePitch R N j r g
  let γ:=g^2*pitchTail R N j r g
  γ*maskedSecondAt P.path B P.p x U+(γ+R.alloy.B.kin.alpha N j)*
    (maskedSitePacket P.path.cubic P.p x U+maskedSitePacket P.path.quartic P.p x U)+
    (Integral.temperature g*p)*maskedPacketsAt Z P.p σ C P.p.threshold (g/Real.sqrt p) x U

def maskSpringCap (G : Gauge) (c : Clip) (D C : ℝ) (d M : ℕ) (γ α β : ℝ) : ℝ:=
  |γ| *quadraticMaskCap G c D+|γ+α| *(D*8+D*16)+|β| *((M:ℝ)*maskRosterPrice C d)

def maskSpringRent (G : Gauge) (c : Clip) (p : BudgetPoint) (u D σ C : ℝ) (d M : ℕ) (γ α β : ℝ) : ℝ:=
  |γ| *quadraticMaskRent G c p u D+|γ+α| *(D*(8*(7+u⁻¹))+D*(16*(9+u⁻¹)))+
  |β| *((M:ℝ)*(maskRosterPrice C d*(1+2*((d:ℝ)+2)+625+σ⁻¹)))

theorem spring_mask_complete (R : Run G) (simple : G.Simple) (heat : Poetry R.family.path.levels) (q : ℕ) :
    ∀ᶠ j : ℕ in atTop,∀N,j≤N→∀ per (σ C : ℝ),0<σ→∀ (Z : SeriesA G),Draw Z σ C→
      ∀d,(∀a∈Z,0<a.grade)→(∀a∈Z,a.grade≤d)→∀r g, |g/Real.sqrt (finitePitch R N j r g)|≤2→
      ∀(x : Site (R.family.side j per)),
      let D:=R.family.path.levels.params j
      let p:=(R.family.path.rep N per j).p
      let γ:=g^2*pitchTail R N j r g
      let α:=R.alloy.B.kin.alpha N j
      let β:=Integral.temperature g*finitePitch R N j r g
      let fee:=(625*(Fintype.card PlaqAxes:ℝ))*R.family.path.levels.clock.forcedAllowance j^q
      let f (U : Config G (R.family.side j per)):=maskedSpringAt R N per j r Z σ C g x U-springAt R N per j r Z g x U
      Measurable f ∧ (∀U,‖f U‖≤ maskSpringCap G D.clip D.paths C d Z.length γ α β) ∧
        (∫U,‖f U‖ ∂scene R.family.path N per j)≤ maskSpringRent G D.clip p D.width D.paths σ C d Z.length γ α β*fee := by
  filter_upwards [spring_mask_quadratic R simple heat q,spring_mask_atom_at R simple heat q,
    spring_mask_packets R simple heat q] with j quad atom roster N live per σ C hs Z draw d lower upper r g c x D p γ α β fee f
  let K:=(R.family.path.rep N per j).path
  let V:=R.family.path.levels
  let n:=R.family.side j per
  let μ:=scene R.family.path N per j
  letI : IsProbabilityMeasure μ:=probability R.makes.wilson live
  have rep : R.family.path.Conv N per j:=R.makes.wilson.represents N per j live
  have lawful:K.Bounds D.clip D.width D.paths (V.clock.loopCap j):=by
    dsimp only [K,D,V];rw [←rep.clip];exact rep.good.paths
  let eqd (U : Config G n):=maskedSecondAt K D.clip p x U-secondAt D.clip K x U
  let cub (U : Config G n):=maskedSitePacket K.cubic p x U-sitePacket K.cubic x U
  let qua (U : Config G n):=maskedSitePacket K.quartic p x U-sitePacket K.quartic x U
  let c0:=g/Real.sqrt (finitePitch R N j r g)
  let zed (U : Config G n):=maskedPacketsAt Z p σ C p.threshold c0 x U-springPacketsAt Z c0 x U
  have same : f=fun U=>(γ*eqd U+(γ+α)*(cub U+qua U))+β*zed U := by
    funext U
    dsimp only [f,maskedSpringAt,springAt,eqd,cub,qua,zed,interactionAt,K,p,D,γ,α,β,c0]
    ring
  rw [same]
  have hq:=quad N live per K D.clip D.width D.paths (V.clock.loopCap j) lawful.width lawful x
  have h3:=atom N live per 3 K.cubic D.width D.paths lawful.width lawful.three x
  have h4:=atom N live per 4 K.quartic D.width D.paths lawful.width lawful.four x
  have hz:=roster N live per σ C c0 hs draw.1 c d Z draw lower upper p x
  have together:=add_mask μ (add_mask μ (scale_mask μ γ hq) (scale_mask μ (γ+α) (add_mask μ h3 h4))) (scale_mask μ β hz)
  refine ⟨together.1,fun U=>(together.2.1 U).trans_eq ?_,together.2.2.trans_eq ?_⟩
  · dsimp only [maskSpringCap];norm_num
  · dsimp only [maskSpringRent];push_cast;ring

end YM.Integration.OriginalMarkedRunAction
