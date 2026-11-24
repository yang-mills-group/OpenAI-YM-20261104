import YM.Integration.WilsonVacuumPreResetCurvatureMoves
import YM.Integration.WilsonVacuumPreResetLiftedPortfolio

/-! The original finite candidate and its signed complement, including all
three curvature ranks and the old physical list of forced supports. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetCurvaturePortfolio
open Filter Lattice RG Wilson PhysicalNext PhysicalNext.Repeat AnalyticBridge VerifiedReset
open Push Push.AbsoluteSums Push.AbsoluteSums.Animals Collection Quotes Song Meadow RG01Estimate RG01Estimate.Precise
open Extra.Iteration Next.Scheduling WilsonStartup Geo
open WilsonVacuumPreResetCurvatureField WilsonVacuumPreResetCurvatureRegister WilsonVacuumPreResetCurvatureRack
open scoped Classical Topology
variable {G:Gauge}{n:Side}

private theorem outside (B:BudgetPoint)(K:PathData G)(c:Clip){σ C Λ:ℝ}(h:K.Bounds c σ C Λ)
    (clip:Decent c B)(reach:preExponent B/B.B≤σ/4)(γ β:ℝ)(q:ℕ):
    Meadow.Budget B (fun i=>strings K B (slot (number n i)))
      (fun i=>if q+1≤arc K (slot (number n i)) then source K c γ β (number n i) else 0)
      (WilsonVacuumPreResetLiftedPiece.rebate σ (q+1)*WilsonVacuumPreResetCurvaturePrice.cost (G:=G) B c σ C γ β):=by
  obtain ⟨f,paid,rows⟩:=WilsonVacuumPreResetCurvaturePrice.long (n:=n) B K c h clip reach γ β (q+1)
  have amend:Real.exp (-(σ/4)*(q+1:ℕ))=WilsonVacuumPreResetLiftedPiece.rebate σ (q+1):=by
    rw [WilsonVacuumPreResetLiftedPiece.rebate,←Real.exp_neg]; congr 1;ring
  refine ⟨fun i=>if q+1≤arc K (slot (number n i)) then f (number n i) else 0,fun x=>?_,?_⟩
  · rw [←amend]
    exact Cost.equiv (number n) (paid x)
  intro i
  by_cases hq:q+1≤arc K (slot (number n i)) <;> simp only [hq,if_true,if_false]
  · exact rows _
  · refine ⟨CouplingShape.reg_const _,?_⟩
    simpa only [abs_zero] using! (CouplingShape.sup_const (G:=G) (p:=B)
      (o:=(strings K B (slot (number n i))).site) (X:=(strings K B (slot (number n i))).support) 0)

theorem original (A:Listing G n)(B:BudgetPoint)(K:PathData G)(c:Clip){σ C Λ:ℝ}(h:K.Bounds c σ C Λ)
    (clip:Decent c B)(reach:preExponent B/B.B≤σ/4)(γ β:ℝ)(q:ℕ){η:ℝ}(ep:0<η):
    ∀ᶠt:ℕ in atTop,let M:=model A B K c σ C γ β t q
      Precise.Suggests B M (WilsonVacuumPreResetLiftedPiece.rebate σ (q+1)*M.bill+η) M.bill:=by
  let X:Listing G n:=⟨fun i=>strings K B (slot (number n i)),A.hard⟩
  let F:=source K c γ β ∘ number n
  let l (i:ℕ):=arc K (slot (number n i))
  let omitted (t i:ℕ):Prop:=l i≤q ∧ t≤code (number n i)
  have full:=invoice (n:=n) B K c h clip reach γ β
  have tail:=outside (n:=n) B K c h clip reach γ β q
  have fee:=Caddy.limits (A:=X) B omitted F full (fun i _=>
    (Filter.eventually_gt_atTop (code (number n i))).mono (fun _ ht h=>ht.not_ge h.2)) ep
  filter_upwards [fee] with t ht
  intro M
  have err:M.trunk-M.pioneers=(fun i=>if q+1≤l i then F i else 0)+(fun i=>if omitted t i then F i else 0):=by
    funext i U
    change F i U-WilsonVacuumPreResetCurvatureRack.held K c γ β (cut n K t q) i U=
      (if q+1≤l i then F i else 0) U+(if omitted t i then F i else 0) U
    simp only [WilsonVacuumPreResetCurvatureRack.held,admitted]
    by_cases numbered:code (number n i)<t <;> by_cases near:l i≤q <;>
      simp [F,l,numbered,near,omitted,show t≤code (number n i) ↔ ¬code (number n i)<t from not_lt.symm,
        show q+1≤l i ↔ ¬l i≤q by omega] at *
  refine ⟨full,?_,?_,WilsonVacuumPreResetCurvatureMoves.original A B K c σ C γ β t q⟩
  · convert Acquire.budget_cut (fun i=>i∈cut n K t q) full using 1 <;> first | rfl | skip
    funext i
    change WilsonVacuumPreResetCurvatureRack.held K c γ β (cut n K t q) i=_
    by_cases hh:i∈cut n K t q <;> simp [WilsonVacuumPreResetCurvatureRack.held,hh]
  · rw [err]
    apply Abacus.pay_bundle B tail
    convert ht using 1
    funext i
    by_cases hi:omitted t i <;> simp [hi]

end YM.Integration.WilsonVacuumPreResetCurvaturePortfolio
