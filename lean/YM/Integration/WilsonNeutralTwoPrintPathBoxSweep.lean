import YM.Integration.WilsonNeutralTwoPrintPathBoxTail

/-! Compare the actual sum over all copies to the independently declared
covered programme on a finite box of relative positions. The two errors decay
in separate variables, the size of this box and the enhanced period. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonNeutralTwoPrintPathBoxSweep
open Filter Function Finset Lattice Wilson RG
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Mer
open WilsonCoeffUV.Soil WilsonCoeffUV.Blue WilsonCoeffUV.Embroider WilsonCoeffUV.Embroider.Canvas
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Winding WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Bank.Mosaic
open Further.PhysicalPeriodLimitF933 Macrame Shingle FVA1Physical TwoReset
open WilsonNeutralTwoPrintPathBoxPlacement (homes box)
open WilsonNeutralTwoPrintPathBoxInk (ink config)
open WilsonNeutralTwoPrintPathBoxTail (finite)
open WilsonNeutralTwoPrintPathPageLedger (price)
open WilsonNeutralTwoPrintPathRankFare (tariff)
open scoped Classical BigOperators Topology
variable {I α V:Type}[DecidableEq I][Fintype α][NormedAddCommGroup V][NormedSpace ℝ V][CompleteSpace V]{r:ℕ}{n X:Side}

def goal (n:Side)(F:Ten V (Cloth α) r)(test:V →L[ℝ] ℂ)(weights:(Fin r→Site n × α)→ℂ):ℂ:=
  ∑x:Fin r→Site n × α,test (plume F n x)*weights x

def retained (n:Side)(S:Finset I)(o:I)(root:Cover)(base:(S.erase o) → Cover)(D:ℕ)
    (F:(I → Cover)→Ten V (Cloth α) r)(test:V →L[ℝ] ℂ)(weights:(Fin r→Site n × α)→ℂ):ℂ:=
  ∑w:box n base D,goal n (F (ink S o root w.val)) test weights

def hearing (h:n.val∣X.val)(S:Finset I)(o:I)(root:Site X)(site:(S.erase o)→Site X)
    (P:(I → Cover)→Ten V (Site X × α) r)(test:V →L[ℝ] ℂ)(weights:(Fin r→Site n × α)→ℂ):ℂ:=
  ∑p:(S.erase o)→Fin (Pages n X),finite h (P (config h S o root site p)) test weights

theorem original (h:n.val∣X.val)(S:Finset I)(o:I)(live:o∈S)(root:Cover)(base:(S.erase o) → Cover)
    (D:ℕ)(room:32*D<X.val)(home:lift (wrap X root)=root)
    (P:(I → Cover)→Ten V (Site X × α) r)(F:(I → Cover)→Ten V (Cloth α) r)(σ A:ℝ)(hs:0<σ)
    (paid:∀y:I → Cover,MarkU y S (P y) (F y) σ A)(test:V →L[ℝ] ℂ)
    (weights:(Fin r→Site n × α)→ℂ)(height:ℝ)(hh:0≤height)(bounded:∀x,‖weights x‖ ≤ height):
    ‖hearing h S o (wrap X root) (homes X root base) P test weights-
      retained n S o root base D F test weights‖≤
      (Real.exp (-((σ/2)/2)*(D:ℝ))*price S o α r σ (‖test‖*A))*height+
      ((box n base D).card*(‖test‖*height*tariff α r σ A))*catchW (σ/512) X:=by
  let small:=∑w:box n base D,finite h (P (ink S o root w.val)) test weights
  have outside:=WilsonNeutralTwoPrintPathBoxTail.original h S o live root base D (by omega) home P σ A hs
    (fun y=>(paid y).bill) test weights height hh bounded
  apply (norm_sub_le_norm_sub_add_norm_sub _ small _).trans (add_le_add outside _)
  change ‖(∑w:box n base D,finite h (P (ink S o root w.val)) test weights)-
    ∑w:box n base D,goal n (F (ink S o root w.val)) test weights‖≤_
  rw [←Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑_w:box n base D,(‖test‖*height*tariff α r σ A)*catchW (σ/512) X:=by
      apply Finset.sum_le_sum
      intro w _
      have seats:=WilsonNeutralTwoPrintPathBoxInk.small S o root base D w
      have width:4*crestCard (ink S o root w.val) S<X.val:=by omega
      exact WilsonNeutralTwoPrintPathCofinalPeg.original h (ink S o root w.val) S o live hs _ _ test
        (paid _) width weights height hh bounded
    _ = _:=by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul,mul_assoc]

end YM.Integration.WilsonNeutralTwoPrintPathBoxSweep
end
