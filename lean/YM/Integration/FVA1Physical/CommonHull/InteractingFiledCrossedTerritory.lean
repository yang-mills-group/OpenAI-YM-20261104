import YM.Integration.FVA1Physical.CommonHull.InteractingFiledTerritoryMeasurable
import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionCrossingInvoice

/-! Original signed crossing invoice on the field's actually reachable short
component. The full compulsory rosters are reassembled before pricing. The
reachable volume is integrated under the same field law. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
namespace YM.Integration.FVA1Physical.Marked.RemoteRoster
open Set Finset MeasureTheory Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Fusion.Attached Exchange Exchange.RoseCut
open Push.AbsoluteSums.Animals
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{V T I:Type}[DecidableEq V]{C:Census V}{o:V→Site n}{P:Rep G n}
  (A:Gallery T I o P C)(t:T)(D:ℕ)(x:Site n)

abbrev cutTerritory(U:Config G n):Support n:=shortTerritory P.activities P.p (fun i=>A.K.hard t i U) x D
abbrev actualCrossing (U:Config G n):Poly C:=crossedCash P.activities P.p U (fun i=>A.K.hard t i U) (cutTerritory A t D x U)

private theorem fixed_cross_borel (K:Support n):Measurable fun U=>crossedCash P.activities P.p U (fun i=>A.K.hard t i U) K:=by
  apply Measurable.tsum;intro S
  by_cases meet:∃i∈S,cross P.activities K i
  · simp only [Set.indicator_of_mem (show S∈{Q:Finset ℕ|∃i∈Q,cross P.activities K i} from meet)]
    exact Measurable.ite (P.activities.admissible_borel P.p S)
      (Finset.measurable_fun_prod _ fun i _=>(A.K.locality t i).borel) measurable_const
  simp only [Set.indicator_of_notMem (show S∉{Q:Finset ℕ|∃i∈Q,cross P.activities K i} from meet)]
  exact measurable_const

theorem actual_crossing_borel:Measurable (actualCrossing A t D x):=by
  let cash:=fun K (U:Config G n)=>crossedCash P.activities P.p U (fun i=>A.K.hard t i U) K
  have equality:actualCrossing A t D x=fun U=>∑K:Support n,if cutTerritory A t D x U=K then cash K U else 0:=by
    funext U;simp only [sum_ite_eq,Finset.mem_univ,if_true];rfl
  rw [equality];exact Finset.measurable_fun_sum _ fun K _=>Measurable.ite (territory_borel A t D x K)
    (fixed_cross_borel A t K) measurable_const

theorem actual_crossing_bound (w:V→ℝ)(wp:∀v,0<w v)(e κ:ℝ)(paid:A.K.Paid w P.p.B e κ)
    (en:0≤e)(small:κ≤1)(U:Config G n):
    Poly.price w (actualCrossing A t D x U)≤(Real.exp (-(e*D))*κ)*(cutTerritory A t D x U).card:=by
  let L:=cutTerritory A t D x U
  let K:=fun i=>A.K.hard t i U
  have tall (i:ℕ)(alive:K i≠0)(across:cross P.activities L i):
      D≤coverNumber P.p.B (P.activities.forced i).support ∧ ∃y∈L,y∈(P.activities.forced i).support:=by
    obtain ⟨z,actor,inL⟩:=not_disjoint_iff.mp across.2
    refine ⟨?_,z,inL,actor⟩
    by_contra! short;apply across.1;intro y on
    have live:shortActors P.activities P.p K D i≠0:=by simpa only [shortActors,if_pos short.le] using alive
    exact mem_filter.mpr ⟨Finset.mem_univ _,Relation.ReflTransGen.tail (mem_filter.mp inL).2 ⟨i,live,actor,on⟩⟩
  exact (crossed_cash_price A w wp e κ paid en small L L D t U tall).trans_eq (by ring)

/-- The complete raw scalar and marked crossing series, with their actual
exterior vacuum actors retained. This probability is the original law. The
only geometric cost comes from two balls of one short-actor width. -/
theorem original_crossing_invoice (μ:Measure (Config G n))[IsProbabilityMeasure μ](event:Set (Config G n))
    (em:MeasurableSet event)(w:V→ℝ)(wp:∀v,0<w v)(e κ:ℝ)(paid:A.K.Paid w P.p.B e κ)
    (en:0≤e)(kp:0≤κ)(small:κ≤1){ρ:ℝ}(rp:0≤ρ)
    (rare:∀Z:Support n,μ.real {U|Z⊆flags P.p.threshold U}≤ρ^Z.card)
    (dilute:(ballCost (2*width P.p D):ℝ)*ρ≤1/2):
    let price:=event.indicator (fun U=>Poly.price w (actualCrossing A t D x U))
    Integrable price μ ∧ (∫U,price U ∂μ)≤Real.exp (-(e*D))*κ*
        (μ.real event+2*(ballCost (width P.p D):ℝ)*((ballCost (2*width P.p D):ℝ)*ρ)):=by
  intro price
  let r:=Real.exp (-(e*D))*κ
  have rp':0≤r:=mul_nonneg (Real.exp_nonneg _) kp
  let pocket:=fun y:Site n=>event∩{U|y∈cutTerritory A t D x U}
  let ticket:=fun y:Site n=>(pocket y).indicator (fun _:Config G n=>(1:ℝ))
  have pm(y):MeasurableSet (pocket y):=em.inter (territory_site_borel A t D x y)
  have ti(y):Integrable (ticket y) μ:=(integrable_const _).indicator (pm y)
  have bill(y):(∫U,ticket y U ∂μ)=μ.real (pocket y):=by
    dsimp only [ticket];rw [integral_indicator (pm y),setIntegral_const];simp
  let gross:=fun U=>r*(∑y:Site n,ticket y U)
  have gi:Integrable gross μ:=(integrable_finsetSum univ (fun y _=>ti y)).const_mul _
  have pn(U):0≤price U:=Set.indicator_nonneg (fun _ _=>Poly.nonnegative wp _) U
  have bound(U):price U≤gross U:=by
    by_cases yes:U∈event
    · rw [show price U=Poly.price w (actualCrossing A t D x U) from Set.indicator_of_mem yes _]
      have each(y):ticket y U=if y∈cutTerritory A t D x U then 1 else 0:=by
        simp only [ticket,pocket,Set.indicator_apply,Set.mem_inter_iff,yes,true_and,Set.mem_setOf_eq]
      simpa only [gross,each,←sum_filter,filter_mem_eq_inter,Finset.univ_inter,sum_const,nsmul_eq_mul,mul_one]
        using actual_crossing_bound A t D x w wp e κ paid en small U
    have each(y):ticket y U=0:=Set.indicator_of_notMem (fun hit=>yes hit.1) _
    simp only [price,Set.indicator_of_notMem yes,gross,each,sum_const_zero,mul_zero,le_refl]
  have pb:Measurable price:=((Poly.price_cont w).measurable.comp (actual_crossing_borel A t D x)).indicator em
  have pi:Integrable price μ:=gi.mono' pb.aestronglyMeasurable (.of_forall fun U=>by
    rw [Real.norm_of_nonneg (pn U)];exact bound U)
  have eq:(∫U,gross U ∂μ)=r*∑y,μ.real (pocket y):=by
    rw [show (∫U,gross U ∂μ)=r*(∫U,∑y:Site n,ticket y U ∂μ) from integral_const_mul ..,
      integral_finsetSum _ (fun y _=>ti y)];simp only [bill]
  refine ⟨pi,(integral_mono pi gi bound).trans ?_⟩
  rw [eq];exact mul_le_mul_of_nonneg_left (original_short_reach A t μ x D event rp rare dilute) rp'

end YM.Integration.FVA1Physical.Marked.RemoteRoster
