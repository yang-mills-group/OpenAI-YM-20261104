import YM.Integration.WilsonOriginalPrimerDischarge

/-! The actual one-name Armada finances its own nonlinear absolute-link
Taylor coefficient. Compared on the purchased directions, it is exactly
the ink of the independently named primary at the same site. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPrimerCourseRead
open Function Filter Finset Lattice Laurent RG Wilson Stationary Primitives.TwoWave
open QuadraticLocal QuadraticLocal.Poetry QuadraticLocal.Sunrise QuadraticLocal.Earn QuadraticLocal.Sunrise.Aviary
open Marker Next.SectorChange Multi Comparison.RG02.Bulk AllOrder AllOrder.Floe
open Further.PhysicalPeriodLimitF933 Macrame Shingle
open AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Ink WilsonCoeffUV WilsonCoeffUV.Blue PowerSeries
open WilsonOlderFreshGraphVote WilsonNeutralRenderedColumn WilsonOlderFreshGraphArmada
open scoped Topology BigOperators Classical
variable {G:Gauge}{n:Side}{Q d:ℕ}
variable {P:Earn.Passport n Unit}{H:Marker.Census Unit}(S:Earn.Binder P H)
variable (W:Fin (Q+1)→Poetry.Roll G Unit)(C:Fin (Q+1)→ℝ)(σ:ℝ)
variable (paid:∀j,(W j).Faith {()} () (j.val+d+2) (2*σ) (C j))
variable (legal:∀j,(W j).honest)(d0:0<d)
variable (E:Unit→Set ℂ)(cap:∀ t,‖value E t‖≤1)
local notation "M" => material S W C σ paid legal d0 (value E)

include cap in
theorem salary (t:Affinity.Wallet E)(σ0:0<σ):Air.Staff M (fun z=>(M z).paint t)
    (fun _=>d) σ (Q+d+1):=by
  let g:=gross S C σ
  let w:=(1+|g|)⁻¹
  have wp:0<w:=by dsimp [w]; positivity
  have bound:w*g≤1:=by
    rw [mul_comm,←div_eq_mul_inv,div_le_one (by positivity)]
    exact (le_abs_self g).trans (by linarith)
  have arm:=WilsonOlderFreshGraphArmada.original S W C σ paid legal d0 E σ0.le cap w wp bound
    (le_refl Q) (seats:=1) le_rfl (le_refl d)
  apply Air.license M _ (fun _=>d) (fun _=>w) arm σ0
  intro z
  exact (WilsonOlderFreshGraphMount.enrolled S _ z.1 d d0 ((paid z.1).pinned z.2.1)
    (legal z.1 z.2.1) z.2.2 σ (value E) cap).1 t

include cap in
theorem original (t:Affinity.Wallet E)(σ0:0<σ)
    (layout:Layout G)(stock:Finset Age)(T:PChart G n)(j:ℕ)
    (agreed:∀ A:Link G n,MvPolynomial.eval A (coeff j (flash T))=
      ∑l:Fin (Q+1),((W l).folded l j).table n (mingle A (WilsonElectedPrimaryTensor.pin S.center)))
    (A:Link G n):
    (Air.discharge (Air.craft M (fun z=>(M z).paint t) (fun _=>d) layout stock) j
      (Stationary.arm G n 1 A)).part (submitted S).val =
        value E t * Complex.ofReal (MvPolynomial.eval A (coeff j (flash T))):=by
  rw [agreed A]
  exact WilsonOriginalPrimerDischarge.filed S W C σ paid legal d0 (value E) t σ0
    (salary S W C σ paid legal d0 E cap t σ0) layout stock A j

end YM.Integration.WilsonOriginalPrimerCourseRead
end
