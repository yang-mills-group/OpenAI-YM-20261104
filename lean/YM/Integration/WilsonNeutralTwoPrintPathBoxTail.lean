import YM.Integration.WilsonNeutralTwoPrintPathBoxInk
import YM.Integration.WilsonNeutralTwoPrintPathCofinalPeg

/-! A finite relative-site cutoff of the actual signed, physically held
numerator. Every omitted tuple retains its own Gaussian and angular roots. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonNeutralTwoPrintPathBoxTail
open Filter Function Finset Lattice Wilson RG
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Mer
open WilsonCoeffUV.Soil WilsonCoeffUV.Blue WilsonCoeffUV.Embroider WilsonCoeffUV.Embroider.Canvas
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Winding WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Bank.Mosaic
open Further.PhysicalPeriodLimitF933 Macrame Shingle FVA1Physical TwoReset
open WilsonNeutralTwoPrintPathBoxPlacement (homes box selected entry)
open WilsonNeutralTwoPrintPathBoxRecount (roster)
open WilsonNeutralTwoPrintPathBoxInk (ink config)
open WilsonNeutralTwoPrintPathPageLedger (price)
open WilsonNeutralTwoPrintPathPageRead (lower)
open WilsonOriginalRelativePageTail (locate)
open scoped Classical BigOperators Topology
variable {I α V:Type}[DecidableEq I][Fintype α][NormedAddCommGroup V][NormedSpace ℝ V]{r:ℕ}{n X:Side}

def finite (h:n.val∣X.val)(P:Ten V (Site X × α) r)(test:V →L[ℝ] ℂ)(weights:(Fin r→Site n × α)→ℂ):ℂ:=
  ∑x:Fin r→Site X × α,test (P x)*weights (lower h ∘ x)

theorem original (h:n.val∣X.val)(S:Finset I)(o:I)(live:o∈S)(root:Cover)(base:(S.erase o) → Cover)
    (D:ℕ)(room:2*D<X.val)(home:lift (wrap X root)=root)
    (P:(I → Cover)→Ten V (Site X × α) r)(σ A:ℝ)(hs:0<σ)
    (gross:∀y:I → Cover,Wig (tor X) (wrap X ∘ y) σ A S (P y))
    (test:V →L[ℝ] ℂ)(weights:(Fin r→Site n × α)→ℂ)(height:ℝ)(hh:0≤height)(cap:∀x,‖weights x‖ ≤ height):
    ‖(∑p:(S.erase o)→Fin (Pages n X),finite h
        (P (config h S o (wrap X root) (homes X root base) p)) test weights)-
      ∑w:box n base D,finite h (P (ink S o root w.val)) test weights‖≤
      (Real.exp (-((σ/2)/2)*(D:ℝ))*price S o α r σ (‖test‖*A))*height:=by
  let pos:=config h S o (wrap X root) (homes X root base)
  let take:=roster h root base D
  let amounts:=fun p=>finite h (P (pos p)) test weights
  let outer:=Finset.univ.filter (fun p=>∃i:S.erase o,D≤ separation (wrap X root) (locate h (homes X root base) p i))
  let K:=fun p=>P (pos p)
  have hats:=WilsonNeutralTwoPrintPathBoxRecount.recount h root base D room amounts
  have kept:∑p∈take,amounts p=∑w:box n base D,finite h (P (ink S o root w.val)) test weights:=by
    apply hats.trans
    apply Finset.sum_congr rfl
    intro w _
    change finite h (P (config h S o (wrap X root) (homes X root base)
      (selected h root base w.val ((entry _ _ _ _).mp w.prop).2))) test weights=_
    rw [config,WilsonNeutralTwoPrintPathBoxRecount.placed h S o root base D room home w]
    rfl
  have missed:(Finset.univ\take)⊆outer:=by
    intro p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,WilsonNeutralTwoPrintPathBoxRecount.absent h root base D p
      (Finset.mem_sdiff.mp hp).2⟩
  have split:(∑p∈Finset.univ\take,amounts p)+(∑p∈take,amounts p)=∑p,amounts p:=
    Finset.sum_sdiff (Finset.subset_univ take)
  have far:=WilsonNeutralTwoPrintPathPageTruncation.original h S o live (wrap X root) (homes X root base)
    σ A hs test K (fun p=>gross (pos p)) D
  change ‖(∑p,amounts p)-_‖≤_
  rw [←kept,←split,add_sub_cancel_right]
  calc
    _ ≤ ∑p∈Finset.univ\take,‖amounts p‖:=norm_sum_le _ _
    _ ≤ ∑p∈outer,‖amounts p‖:=Finset.sum_le_sum_of_subset_of_nonneg missed (fun p _ _=>norm_nonneg _)
    _ ≤ ∑p∈outer,(∑x:Fin r→Site X × α,‖test (K p x)‖)*height:=by
      apply Finset.sum_le_sum
      intro p _
      rw [Finset.sum_mul]
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro x _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (cap _) (norm_nonneg _)
    _ ≤ _:=by
      rw [←Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right far hh

end YM.Integration.WilsonNeutralTwoPrintPathBoxTail
end
