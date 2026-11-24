import YM.Integration.WilsonOriginalPrimerReplicatedInk

/-! The complete counted copied teacher supplies its actual finite
Gaussian numerator on each enlarged physical period, with its unchanged source. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPrimerCopiedRay
open Function Filter Finset Lattice Laurent RG Wilson Stationary Primitives.TwoWave
open QuadraticLocal QuadraticLocal.Poetry QuadraticLocal.Sunrise QuadraticLocal.Earn QuadraticLocal.Sunrise.Aviary
open Marker Next.SectorChange Multi Comparison.RG02 AllOrder AllOrder.Floe
open Further.PhysicalPeriodLimitF933 Macrame Shingle Precision Tree Exterior PhysicalNext.Repeat.Legato
open AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Ink WilsonCoeffUV WilsonCoeffUV.Blue PowerSeries
open WilsonOlderFreshGraphVote WilsonNeutralRenderedColumn WilsonOlderFreshGraphArmada FVA1Physical.TwoReset
open WilsonVacuumPreResetStationaryChange WilsonOriginalPrimerReplicatedFields
open WilsonOriginalPrimerReplicatedInk
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
attribute [local instance] Gauge.frobInner
variable {G:Gauge}(R:Run G)(N i per:ℕ)(hi:i<N)(F:Forest (step R i per).ratio)
variable {n:Side}(h:n.val∣(fine R i per).val){Q d:ℕ}{P:Earn.Passport n Unit}{H:Marker.Census Unit}
variable (S:Earn.Binder P H)(W:Fin (Q+1)→Poetry.Roll G Unit)(C:Fin (Q+1)→ℝ)(σ:ℝ)
variable (paid:∀j,(W j).Faith {()} () (j.val+d+2) (2*σ) (C j))
variable (legal:∀j,(W j).honest)(d0:0<d)
variable (E:Unit→Set ℂ)(cap:∀ t,‖value E t‖≤1)(t:Affinity.Wallet E)(σ0:0<σ)
variable (layout:Layout G)(stock:Finset Age)(T:Site (fine R i per)→PChart G (fine R i per))(r:ℕ)
variable (shell:∀x,shellK d (T x))(pure:∀x,∀j,Pure (T x j))
variable (agreed:∀ l≤r,∀ x:Site (fine R i per),∀ A:Link G (fine R i per),MvPolynomial.eval A (coeff l (flash (T x)))=
   ∑k:Fin (Q+1),((W k).folded k l).table (fine R i per) (mingle A (WilsonElectedPrimaryTensor.pin x)))
local notation "M" => material S W C σ paid legal d0 (value E)
include cap σ0 shell pure agreed

theorem original (B:fieldDir G (coarse R i per) 1):
    WilsonOriginalEarnedUnaryPage.Ray R N i per hi F
      (copyColor h M (fun _=>d) (fun z=>(M z).paint t) layout stock)
      B (submitted S) (value E t) (located h S.center T) r:=by
  let Y:=copyColor h M (fun _=>d) (fun z=>(M z).paint t) layout stock
  let chart:=located h S.center T
  have g:=graded h S W C σ paid legal d0 E cap t σ0 layout stock (submitted S)
  have filed:=sheets h S.center T shell pure
  intro name j hj z
  by_cases named:name=submitted S
  · subst name
    rw [if_pos rfl]
    have common(k:ℕ)(hk:k≤j)(A:Link G (fine R i per)):
        (Air.discharge Y k (Stationary.arm G (fine R i per) 1 A)).part (submitted S).val =
        value E t * Complex.ofReal (MvPolynomial.eval A (coeff k (flash chart))):=by
      change (Air.discharge (copyColor h M (fun _=>d) (fun z=>(M z).paint t) layout stock) k _).part _=_
      rw [discharge h S W C σ paid legal d0 E cap t σ0 layout stock (submitted S)]
      change _=value E t * Complex.ofReal (MvPolynomial.eval A (coeff k (flash (located h S.center T))))
      rw [filed.2.2,map_sum,map_sum,Complex.ofReal_sum,Finset.mul_sum]
      apply Finset.sum_congr rfl;intro u _
      exact WilsonOriginalPrimerCourseRead.original (lifted h S u) W C σ paid legal d0 E cap t σ0 layout stock
        (T (page h S.center u).val) k (agreed k (hk.trans hj) _) A
    have e:=WilsonOriginalPrimerForestRead.original (V:=Unit) (C:=H) R N i per hi F Y (submitted S) (value E t) chart j g common B z
    simpa only [PhysicalForestRay.sample,OriginalRadialSeries.observed,coeff_map] using e
  · rw [if_neg named]
    have dead:PhysicalForestMarkedRay.chartMark (step R i per) F (saddle R N i per F)
        (model R N i per hi) B z Y name=0:=by
      funext s
      exact elsewhere h S W C σ paid legal d0 E t layout stock name named s _
    change PhysicalForestMarkedRay.readJet (Y.power name+j) (PhysicalForestMarkedRay.chartMark (step R i per) F (saddle R N i per F) (model R N i per hi) B z Y name)=0
    rw [dead]
    simp [PhysicalForestMarkedRay.readJet,Function.comp_def]

end YM.Integration.WilsonOriginalPrimerCopiedRay
end
