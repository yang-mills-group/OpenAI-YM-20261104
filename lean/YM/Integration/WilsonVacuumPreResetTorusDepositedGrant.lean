import YM.Integration.WilsonVacuumPreResetTorusDeposit
import YM.Integration.WilsonVacuumPreResetTorusGrant
import YM.Integration.FundedInteractingPeriod

/-! On every fine configuration the deposited vacuum is the same original
group-field function that enters the independent finite torus integrand. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetTorusDepositedGrant
open Function Filter Finset Lattice RG Wilson Gauge Pressure Precision Tree
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Ker AllOrder.Ker.Start
open AllOrder.Ink Ink.Money Extra.Iteration AllOrder.Floe.StateE
open Comparison.RG02 WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open Bloch Exterior Stationary Matrix WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open FreeResolvent WilsonStartup LocalComparison.Global IterationFour.Vacuum
open WilsonVacuumPreResetTorusDeposit
open scoped Classical BigOperators

variable {G:Gauge}{n:Side}

theorem money (Z:SeriesA G){cap:ℕ}{σ C:ℝ}(width:0<σ)(draw:Draw Z σ C)
    (low:∀a∈Z,3≤a.grade)(high:∀a∈Z,a.grade≤cap)(s:ℝ)(U:Config G n):
    QuadraticLocal.Fk.money (bank Z) (Step.tape cap) s U=FundedPeriodAction.rendered n Z s U:=by
  induction Z with
  | nil => simp [QuadraticLocal.Fk.money,sketch,WilsonVacuumPreResetTorusDeposit.bank,Extra.Iteration.action,Patch.average,Precision.uncut,
      Atom.unmasked,Extra.Iteration.blank,Atom.poly,FundedPeriodAction.rendered]
  | cons a T ih =>
    have old:Draw T σ C:=⟨draw.1,fun b hb=>draw.2 b (List.mem_cons_of_mem _ hb)⟩
    have lows (b:PrismA G)(hb:b∈T):3≤b.grade:=low b (List.mem_cons_of_mem _ hb)
    have budget:=quoted T old.2 (fun b hb=>by have:=lows b hb; omega) (address a)
    have ga:=coordinates a (low a (List.mem_cons_self ..))
    have registered:address a∈Step.tape cap:=by
      apply Age.in_scope.mpr
      rw [ga.1]
      exact high a (List.mem_cons_self ..)
    have elapsed:(address a).stamp=a.grade-a.rise:=by
      unfold Age.stamp
      rw [ga.1,ga.2]
      omega
    let v:=s^(a.grade-a.rise)*FundedPeriodAction.action n a U
    have term (i:Age):sketch (bank (a::T)) i n s U=
        (if address a=i then v else 0)+sketch (bank T) i n s U:=by
      by_cases hit:address a=i
      · subst i
        have add:=action_join width (draw.2 a (List.mem_cons_self ..)).toll budget.pay U
        have addition:Extra.Iteration.action (WilsonVacuumPreResetTorusDeposit.bank (a::T) (address a)) U=
            Extra.Iteration.action a.cells U+
            Extra.Iteration.action (WilsonVacuumPreResetTorusDeposit.bank T (address a)) U:=by
          simp only [WilsonVacuumPreResetTorusDeposit.bank]
          exact add
        simp only [sketch,Pi.smul_apply,smul_eq_mul,if_true,elapsed]
        exact (congrArg (fun u:ℝ=>s^(a.grade-a.rise)*u) addition).trans (mul_add ..)
      · simp only [sketch,WilsonVacuumPreResetTorusDeposit.bank,dif_neg hit,if_neg hit,zero_add]
    simp only [QuadraticLocal.Fk.money,Finset.sum_apply]
    rw [Finset.sum_congr rfl (fun i _=>term i),Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq,if_pos registered]
    have tail:=ih old lows (fun b hb=>high b (List.mem_cons_of_mem _ hb))
    have payment:(∑i∈Step.tape cap,sketch (bank T) i n s U)=FundedPeriodAction.rendered n T s U:=by
      simpa only [QuadraticLocal.Fk.money,Finset.sum_apply] using tail
    rw [payment]
    rfl

theorem colors {V:Type} [DecidableEq V] {J:Marker.Census V}(Q:Bulk.Colors J G n)
    (B:BudgetPoint)(Z:SeriesA G){cap:ℕ}{σ C:ℝ}(width:0<σ)(draw:Draw Z σ C)
    (low:∀a∈Z,3≤a.grade)(high:∀a∈Z,a.grade≤cap):
    QuadraticLocal.Fk.grant (bank Z) (Step.tape cap) Q=FundedInteractingPeriod.colors Q B σ C Z:=by
  have same:QuadraticLocal.Fk.money (bank Z) (Step.tape cap)=
      ActualGradedVacuum.restored (Z.map (FundedCorrectedPeriod.piece n B σ C)):=by
    funext s U
    exact (money Z width draw low high s U).trans (FundedCorrectedPeriod.restored Z draw
      (fun a ha=>by have:=low a ha; omega) width B s U).symm
  unfold QuadraticLocal.Fk.grant FundedInteractingPeriod.colors
  rw [same]

theorem absolute {c f:Side}{V:Type}[DecidableEq V]{J:Marker.Census V}
    (S:StepData c f)(F:Forest S.ratio)(M:Matrix (Woods G f) (Woods G c) ℝ)
    (O:ChartRatio G)(B:Clip)(K:PathData G)(Q:Bulk.Colors J G f)(p:BudgetPoint)
    (Z:SeriesA G){cap:ℕ}{σ C:ℝ}(width:0<σ)(draw:Draw Z σ C)
    (low:∀a∈Z,3≤a.grade)(high:∀a∈Z,a.grade≤cap)(g:ℝ)(w:Sloc S F G):
    PhysicalForestAction.absoluteAction S F M (p:=B) (P:=K) (O:=O)
        (QuadraticLocal.Fk.grant (bank Z) (Step.tape cap) Q) g w =
      FundedInteractingPeriod.potential B K Z g (PhysicalForestAction.field S F M w)+
        jointPen G S (panSlice G S F M *ᵥ w)-g^2*unhaar O (camSlice G S F M *ᵥ w):=by
  rw [colors Q p Z width draw low high]
  exact FundedInteractingPeriod.absolute S F M B K Q Z draw (fun a ha=>by have:=low a ha; omega)
    width p g w

end YM.Integration.WilsonVacuumPreResetTorusDepositedGrant
