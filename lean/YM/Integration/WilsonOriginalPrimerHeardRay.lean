import YM.Integration.WilsonOriginalPrimerForestRead
import YM.Integration.WilsonOriginalEarnedUnaryPage

/-! The true enrolled primary word supplies the full physical forest-ray
page for the measured conditional Wick integral. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPrimerHeardRay
open Function Filter Finset Lattice Laurent RG Wilson Stationary Primitives.TwoWave
open QuadraticLocal QuadraticLocal.Poetry QuadraticLocal.Sunrise QuadraticLocal.Earn QuadraticLocal.Sunrise.Aviary
open Marker Next.SectorChange Multi Comparison.RG02 AllOrder AllOrder.Floe
open Further.PhysicalPeriodLimitF933 Macrame Shingle Precision Tree Exterior PhysicalNext.Repeat.Legato
open AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Ink WilsonCoeffUV WilsonCoeffUV.Blue PowerSeries
open WilsonOlderFreshGraphVote WilsonNeutralRenderedColumn WilsonOlderFreshGraphArmada
open WilsonVacuumPreResetStationaryChange
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
attribute [local instance] Gauge.frobInner

section input
variable {G:Gauge}{n:Side}{Q d:ℕ}
variable {P:Earn.Passport n Unit}{H:Marker.Census Unit}(S:Earn.Binder P H)
variable (W:Fin (Q+1)→Poetry.Roll G Unit)(C:Fin (Q+1)→ℝ)(σ:ℝ)
variable (paid:∀j,(W j).Faith {()} () (j.val+d+2) (2*σ) (C j))
variable (legal:∀j,(W j).honest)(d0:0<d)
variable (E:Unit→Set ℂ)(t:Affinity.Wallet E)(layout:Layout G)(stock:Finset Age)
local notation "M" => material S W C σ paid legal d0 (value E)

def source :Bulk.Colors H G n:=Air.craft M (fun z=>(M z).paint t) (fun _=>d) layout stock

theorem elsewhere (u:Hot H)(hu:u≠submitted S)(s:ℝ)(U:Config G n):
    (source S W C σ paid legal d0 E t layout stock).mark u s U=0:=by
  unfold source Air.craft QuadraticLocal.Fk.grant Air.sums
  apply HasSum.tsum_eq
  apply hasSum_zero.congr_fun
  intro i
  have ne:(ScatterR.actor M i).val≠u.val:=fun eq=>hu (Subtype.ext eq.symm)
  simp [ne]

end input

variable {G:Gauge}(R:Run G)(N i per:ℕ)(hi:i<N)(F:Forest (step R i per).ratio)
variable {Q d:ℕ}{P:Earn.Passport (fine R i per) Unit}{H:Marker.Census Unit}(S:Earn.Binder P H)
variable (W:Fin (Q+1)→Poetry.Roll G Unit)(C:Fin (Q+1)→ℝ)(σ:ℝ)
variable (paid:∀j,(W j).Faith {()} () (j.val+d+2) (2*σ) (C j))
variable (legal:∀j,(W j).honest)(d0:0<d)
variable (E:Unit→Set ℂ)(cap:∀ t,‖value E t‖≤1)(t:Affinity.Wallet E)(σ0:0<σ)
variable (layout:Layout G)(stock:Finset Age)(T:PChart G (fine R i per))(r:ℕ)
variable (agreed:∀ l≤r,∀ A:Link G (fine R i per),MvPolynomial.eval A (coeff l (flash T))=
   ∑k:Fin (Q+1),((W k).folded k l).table (fine R i per) (mingle A (WilsonElectedPrimaryTensor.pin S.center)))
include cap σ0 agreed

theorem original (B:fieldDir G (coarse R i per) 1):
    WilsonOriginalEarnedUnaryPage.Ray R N i per hi F (source S W C σ paid legal d0 E t layout stock)
      B (submitted S) (value E t) T r:=by
  let M:=material S W C σ paid legal d0 (value E)
  let Y:=source S W C σ paid legal d0 E t layout stock
  have salary:=WilsonOriginalPrimerCourseRead.salary S W C σ paid legal d0 E cap t σ0
  have g:Assembly.GradeAt (Y.power (submitted S)) (Bulk.projected (Y.mark (submitted S))):=Air.grade M (fun z=>(M z).paint t) (fun _=>d) salary layout stock (submitted S)
  intro u l hl z
  by_cases h:u=submitted S
  · subst u
    rw [if_pos rfl]
    have known(k:ℕ)(hk:k≤l)(A:Link G (fine R i per)):
        (Air.discharge Y k (Stationary.arm G (fine R i per) 1 A)).part (submitted S).val =
        value E t * Complex.ofReal (MvPolynomial.eval A (coeff k (flash T))) :=
      WilsonOriginalPrimerCourseRead.original S W C σ paid legal d0 E cap t σ0 layout stock T k (agreed k (hk.trans hl)) A
    have e:=WilsonOriginalPrimerForestRead.original (V:=Unit) (C:=H) R N i per hi F Y (submitted S) (value E t) T l g known B z
    simpa only [PhysicalForestRay.sample,OriginalRadialSeries.observed,coeff_map] using e
  · rw [if_neg h]
    have zero:PhysicalForestMarkedRay.chartMark (step R i per) F (saddle R N i per F)
        (model R N i per hi) B z Y u=0:=by
      funext s
      exact elsewhere S W C σ paid legal d0 E t layout stock u h s _
    change PhysicalForestMarkedRay.readJet (Y.power u+l) (PhysicalForestMarkedRay.chartMark (step R i per) F (saddle R N i per F) (model R N i per hi) B z Y u)=0
    rw [zero]
    simp [PhysicalForestMarkedRay.readJet,Function.comp_def]

end YM.Integration.WilsonOriginalPrimerHeardRay
end
