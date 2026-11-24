import YM.Integration.WilsonOriginalPrimerReceipts
import YM.Integration.WilsonNeutralRenderedColumn
import YM.QuadraticLocal.Fk.Offer

/-! On the actual paid source, the signed absolute-link Taylor coefficient of
the original nonlinear Wilson teacher is the sum of its registered folded
curvature words. The full nonlinear teacher and its complete denominator
remain available for the subsequent conditional Laplace operation. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPrimerDischarge
open Function Filter Finset Lattice Laurent RG Wilson Stationary Primitives.TwoWave
open QuadraticLocal QuadraticLocal.Poetry QuadraticLocal.Sunrise QuadraticLocal.Earn QuadraticLocal.Sunrise.Aviary
open Marker Next.SectorChange Multi Comparison.RG02.Bulk AllOrder AllOrder.Floe
open Further.PhysicalPeriodLimitF933 Macrame Shingle
open AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Ink
open WilsonOlderFreshGraphVote WilsonNeutralRenderedColumn
open scoped Topology BigOperators Classical
variable {G:Gauge}{n:Side}{Q d:ℕ}{α:Type}
variable {P:Earn.Passport n Unit}{H:Marker.Census Unit}(S:Earn.Binder P H)
variable (W:Fin (Q+1)→Poetry.Roll G Unit)(C:Fin (Q+1)→ℝ)(σ:ℝ)
variable (paid:∀j,(W j).Faith {()} () (j.val+d+2) (2*σ) (C j))
variable (legal:∀j,(W j).honest)(d0:0<d)(weight:α→ℂ)
local notation "M" => material S W C σ paid legal d0 weight

theorem filed (t:α)(σ0:0<σ){b:ℝ}{B:ℕ}
    (salary:Air.Staff M (fun z=>(M z).paint t) (fun _=>d) b B)
    (layout:Layout G)(stock:Finset Age)(A:Link G n)(j:ℕ):
    (Air.discharge (Air.craft M (fun z=>(M z).paint t) (fun _=>d) layout stock) j
      (Stationary.arm G n 1 A)).part (submitted S).val =
    weight t * (∑l:Fin (Q+1),((W l).folded l j).table n (mingle A (WilsonElectedPrimaryTensor.pin S.center)):ℝ):=by
  let h (z:Name W):=WilsonOriginalPrimerReceipts.head ((W z.1).leg z.2.1) S.center z.1 j A
  let u (z:Name W):=weight t * Complex.ofReal (h z)
  have realSum:=Air.basis M (fun z=>(M z).paint t) (fun _=>d) salary layout stock A (submitted S) j
  have joined:HasSum u ((Air.discharge (Air.craft M (fun z=>(M z).paint t) (fun _=>d) layout stock) j
      (Stationary.arm G n 1 A)).part (submitted S).val):=by
    apply realSum.congr_fun
    intro z
    rw [Poly.part_send,if_pos (show (submitted S).val=(M z).mode from rfl)]
    exact (WilsonOriginalPrimerReceipts.painted S W C σ paid legal d0 weight z t j A).symm
  rw [←joined.tsum_eq,joined.summable.tsum_sigma,tsum_fintype,Complex.ofReal_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  change (∑' z:{k:(W l).Ty // 0<((W l).leg k).atom.magnitude},weight t * Complex.ofReal
    (WilsonOriginalPrimerReceipts.head ((W l).leg z.1) S.center l j A))=_
  rw [tsum_mul_left,←Complex.ofReal_tsum,(WilsonOriginalPrimerReceipts.located (W l) l d j d0
    (by positivity : 0<2*σ) (paid l) S.center A).tsum_eq]

end YM.Integration.WilsonOriginalPrimerDischarge
end
