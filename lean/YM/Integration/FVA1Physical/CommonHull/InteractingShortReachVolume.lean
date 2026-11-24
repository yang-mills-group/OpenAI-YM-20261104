import YM.Integration.FVA1Physical.CommonHull.InteractingFailedPathCount
import Mathlib.Algebra.Order.Ring.GeomSum

/-! An anchored component of genuinely flagged sites has a controlled expected
number of reachable sites. Different branches can reuse the same failures.
Only the number of continuations of one step enters the estimate. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Marked.RemoteRoster
open Set Finset MeasureTheory
open scoped Classical BigOperators
variable {α X:Type*}[Fintype α][DecidableEq α][MeasurableSpace X]

def endSite (x:α):List α→α
  | []=>x
  | y::L=>endSite y L

/-- From a fixed site each occupied endpoint is close to the last of an
ordered list of distinct actual failures. Sum the incidences of each final
ball only once per list, before summing the geometric series over lengths. -/
theorem expected_reach (μ:Measure X)[IsProbabilityMeasure μ](next rim:α→Finset α)(M J:ℕ)
    (degree:∀z,(next z).card≤M)(endpoints:∀z,(rim z).card≤J)(x:α)(N:ℕ)
    (hit:Set X)(link:α→Set X)(E:Finset α→Set X){ρ:ℝ}(positive:0≤ρ)
    (rare:∀D,μ.real (E D)≤ρ^D.card)(small:(M:ℝ)*ρ≤1/2)
    (witness:∀y U,U∈link y → y=x ∨ ∃k∈range N, ∃L∈pathBook next x (k+1),
      L.Nodup ∧ U∈E L.toFinset ∧ y∈rim (endSite x L)):
    (∑y,μ.real (hit∩link y))≤μ.real hit+2*(J:ℝ)*((M:ℝ)*ρ):=by
  let row:=fun k=>(pathBook next x (k+1)).filter List.Nodup
  let evt:=fun y (L:List α)=>if y∈rim (endSite x L) then E L.toFinset else ∅
  let fee:=fun y k (L:List α)=>if y∈rim (endSite x L) then ρ^(k+1) else 0
  let η:ℝ:=(M:ℝ)*ρ
  have yp:0≤η:=mul_nonneg (Nat.cast_nonneg _) positive
  have base (y:α):μ.real (hit∩link y)≤(if y=x then μ.real hit else 0)+∑k∈range N,∑L∈row k,fee y k L:=by
    by_cases same:y=x
    · rw [if_pos same]
      have non:0≤(∑k∈range N,∑L∈row k,fee y k L):=sum_nonneg fun _ _=>sum_nonneg fun L _=>
        by dsimp only [fee];split <;> positivity
      exact (measureReal_mono Set.inter_subset_left (measure_ne_top μ _)).trans (le_add_of_nonneg_right non)
    rw [if_neg same,zero_add]
    have enclosed:hit∩link y⊆⋃k∈range N,⋃L∈row k,evt y L:=by
      intro U hu
      obtain ⟨k,km,L,lm,unique,flags,site⟩:=(witness _ U hu.2).resolve_left same
      exact Set.mem_iUnion.mpr ⟨k,Set.mem_iUnion.mpr ⟨km,Set.mem_iUnion.mpr ⟨L,Set.mem_iUnion.mpr
        ⟨mem_filter.mpr ⟨lm,unique⟩,by simpa only [evt,if_pos site] using flags⟩⟩⟩⟩
    refine (measureReal_mono enclosed (measure_ne_top μ _)).trans ((measureReal_biUnion_finset_le _ _).trans ?_)
    refine sum_le_sum fun k _=>(measureReal_biUnion_finset_le _ _).trans (sum_le_sum fun L listed=>?_)
    by_cases site:y∈rim (endSite x L)
    · simp only [evt,fee,if_pos site]
      obtain ⟨booked,unique⟩:=mem_filter.mp listed
      simpa only [List.toFinset_card_of_nodup unique,path_book_length next x (k+1) booked] using rare L.toFinset
    simp only [evt,fee,if_neg site,measureReal_empty,le_refl]
  have single (k:ℕ)(L:List α):(∑y,fee y k L)≤(J:ℝ)*ρ^(k+1):=by
    simp only [fee,←sum_filter,filter_mem_eq_inter,Finset.univ_inter,sum_const,nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (endpoints _)) (pow_nonneg positive _)
  have level(k:ℕ):(∑L∈row k,∑y,fee y k L)≤(J:ℝ)*η^(k+1):=calc
    _≤∑_L∈row k,(J:ℝ)*ρ^(k+1):=sum_le_sum fun L _=>single k L
    _=(J:ℝ)*((row k).card*ρ^(k+1)):=by simp only [sum_const,nsmul_eq_mul];ring
    _≤(J:ℝ)*((M:ℝ)^(k+1)*ρ^(k+1)):=by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg positive _)
      exact_mod_cast (card_filter_le _ _).trans (path_book_size next M degree x (k+1))
    _=(J:ℝ)*η^(k+1):=by rw [mul_pow]
  have geom:(∑k∈range N,η^(k+1))≤2*η:=by
    have val:=geom_sum_mul η N
    have non:0≤(∑k∈range N,η^k):=sum_nonneg fun k _=>pow_nonneg yp k
    have total:(∑k∈range N,η^k)≤2:=by
      nlinarith only [val,pow_nonneg yp N,mul_nonneg non (sub_nonneg.mpr small)]
    simp only [pow_succ,←sum_mul];exact mul_le_mul_of_nonneg_right total yp
  calc
    _≤∑y,((if y=x then μ.real hit else 0)+∑k∈range N,∑L∈row k,fee y k L):=sum_le_sum fun y _=>base y
    _=μ.real hit+∑k∈range N,∑L∈row k,∑y,fee y k L:=by
      rw [sum_add_distrib];simp only [sum_ite_eq',Finset.mem_univ,if_true]
      congr 1;rw [sum_comm];apply sum_congr rfl;intro k _;rw [sum_comm]
    _≤μ.real hit+∑k∈range N,(J:ℝ)*η^(k+1):=add_le_add_right (sum_le_sum fun k _=>level k) _
    _≤μ.real hit+2*(J:ℝ)*((M:ℝ)*ρ):=by
      rw [←mul_sum];exact add_le_add_right ((mul_le_mul_of_nonneg_left geom (Nat.cast_nonneg J)).trans_eq (by ring)) _

end YM.Integration.FVA1Physical.Marked.RemoteRoster
