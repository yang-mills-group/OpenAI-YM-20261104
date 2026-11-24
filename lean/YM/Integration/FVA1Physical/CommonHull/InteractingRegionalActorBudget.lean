import YM.Integration.FVA1Physical.CommonHull.InteractingNestedOriginalGas

/-! Fund every crossed roster simultaneously from its actual compulsory
inventory. An active actor crosses the retained short component only if it
pays the full cover cutoff. No distinguished accident or site is counted. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace YM.Integration.FVA1Physical.Marked.RemoteRoster
open Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Fusion.Attached Exchange Exchange.RoseCut
open Push.AbsoluteSums Push.Corrected SectorNext.Vacuum
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{V T I:Type}[DecidableEq V]{C:Census V}{o:V→Site n}{P:Rep G n}

private theorem compulsory_bill (B:Activities G n)(E:Support n)(f:ℕ→ℝ)(pn:∀i,0≤f i)
    {κ:ℝ}(kp:0≤κ)(sm:κ≤1)(hit:∀x,SumBudget (fun i=>if x∈(B.forced i).support then f i else 0) κ)
    (v:Finset ℕ→ℝ)(vn:∀S,0≤v S)(purchase:∀S,v S≠0→Regional B E S ∧ S.Nonempty ∧ v S≤∏i∈S,f i):
    SumBudget v κ:=by
  apply budget_of_sum vn
  intro Q
  let X:=fun i=>(B.forced i).support
  let Z:=fun i=>(B.forced i).inventory
  by_cases empty:E=∅
  · have no (s:Finset ℕ):v s=0:=by
      by_contra alive
      obtain ⟨good,⟨i,hi⟩,_⟩:=purchase s alive
      obtain ⟨z,hz⟩:=(B.forced i).inventory_ne
      exact notMem_empty z ((good.2.trans empty) ▸ (mem_biUnion.mpr ⟨i,hi,hz⟩))
    simp only [no,sum_const_zero];exact kp
  let A:=Q.filter fun s=>v s≠0
  let ids:=Q.biUnion id
  have all:A⊆ids.powerset.filter (accounted X Z E):=by
    intro s hs;obtain ⟨inQ,alive⟩:=mem_filter.mp hs
    refine mem_filter.mpr ⟨mem_powerset.mpr (fun i hi=>mem_biUnion.mpr ⟨s,inQ,hi⟩),?_⟩
    refine ⟨(purchase s alive).1.1,?_⟩
    rw [←(purchase s alive).1.2];ext z;simp only [mem_biUnion,Z]
  have replace:(∑s∈Q,v s)=∑s∈A,v s:=by
    symm;apply sum_subset (filter_subset _ _);intro s h no
    by_contra alive;exact no (mem_filter.mpr ⟨h,alive⟩)
  rw [replace]
  apply (sum_le_sum (fun s hs=>(purchase s (mem_filter.mp hs).2).2.2)).trans
  apply (sum_le_sum_of_subset_of_nonneg all (fun s _ _=>prod_nonneg (fun i _=>pn i))).trans
  have fee:=cover_power (γ:=0) X Z (fun i=>(B.forced i).inventory_sup) (fun i=>(B.forced i).inventory_ne)
    sm f pn ?site E ids
  · simpa only [neg_zero,zero_mul,Real.exp_zero,mul_one,if_neg empty] using fee
  case site =>
    intro x K;apply le_trans _ (budget_sum (hit x) K);apply sum_le_sum;intro i _
    simp only [zero_mul,Real.exp_zero,mul_one]
    split_ifs with yes poss
    · exact le_rfl
    · exact (poss ((B.forced i).inventory_sup yes)).elim
    · exact pn i
    exact le_rfl

/-- The same physical wage table pays the complete original crossed
subseries on ANY prescribed inventory, with every proper and quiet face
kept together and an exponential payment for its long cover. -/
theorem original_crossed_rows (A:Gallery T I o P C)(t:T)(U:Config G n)(x:Site n)(D:ℕ)
    (w:V→ℝ)(wp:∀v,0<w v)(e κ:ℝ)(paid:A.K.Paid w P.p.B e κ)(en:0≤e)(kp:0≤κ)(sm:κ≤1)(E:Support n):
    let K:=fun i=>A.K.hard t i U
    let L:=cutTerritory A t D x U
    SumBudget (fun S:Finset ℕ=>Real.exp (e*D)*Poly.price w
      (if ∃i∈S,cross P.activities L i then component P.activities E K S else 0)) κ:=by
  intro K L
  obtain ⟨d,dom,hit⟩:=paid.wages
  let c:=fun i=>Poly.price w (d i)
  let wt:=fun i=>Real.exp (e*coverNumber P.p.B (P.activities.forced i).support)
  let b:=fun i=>c i*wt i
  have cp(i):0≤c i:=Poly.nonnegative wp _
  have wn(i):1≤wt i:=Real.one_le_exp (mul_nonneg en (Nat.cast_nonneg _))
  have bp(i):0≤b i:=mul_nonneg (cp i) (Real.exp_nonneg _)
  have hs(x):SumBudget (fun i=>if x∈(P.activities.forced i).support then b i else 0) κ:=hit x
  have tall(i)(nz:K i≠0)(cr:cross P.activities L i):D≤coverNumber P.p.B (P.activities.forced i).support:=by
    obtain ⟨z,hz,reach⟩:=not_disjoint_iff.mp cr.2
    by_contra! short
    apply cr.1;intro v hv
    have alive:shortActors P.activities P.p K D i≠0:=by simpa only [shortActors,if_pos short.le] using nz
    exact mem_filter.mpr ⟨mem_univ _,Relation.ReflTransGen.tail (mem_filter.mp reach).2 ⟨i,alive,hz,hv⟩⟩
  apply compulsory_bill P.activities E b bp kp sm hs _ (fun S=>mul_nonneg (Real.exp_nonneg _) (Poly.nonnegative wp _))
  intro S alive
  by_cases across:∃i∈S,cross P.activities L i
  swap
  · exact (alive (by simp only [if_neg across,Poly.zero_price,mul_zero])).elim
  by_cases good:Regional P.activities E S
  swap
  · exact (alive (by simp only [if_pos across,component,if_neg good,Poly.zero_price,mul_zero])).elim
  obtain ⟨i,used,cr⟩:=across
  have met:∃j∈S,cross P.activities L j:=⟨i,used,cr⟩
  have nz:K i≠0:=by
    intro dead
    have kill:(∏j∈S,K j)=0:=prod_eq_zero used dead
    exact alive (by simp only [if_pos met,component,if_pos good,kill,Poly.zero_price,mul_zero])
  refine ⟨good,⟨i,used⟩,?_⟩
  rw [if_pos met,component,if_pos good]
  have scale:Real.exp (e*D)≤wt i:=Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (tall i nz cr)) en)
  have wc(j):Poly.price w (K j)≤c j:=(dom j t U).reprice w wp
  have tail(j):c j≤b j:=le_mul_of_one_le_right (cp j) (wn j)
  apply (mul_le_mul_of_nonneg_left (Poly.multiple wp S K) (Real.exp_nonneg _)).trans
  apply (mul_le_mul_of_nonneg_left (prod_le_prod (fun j _=>Poly.nonnegative wp _) (fun j _=>wc j)) (Real.exp_nonneg _)).trans
  rw [←mul_prod_erase S c used,←mul_prod_erase S b used,←mul_assoc]
  have head:Real.exp (e*D)*c i≤b i:=by rw [mul_comm];exact mul_le_mul_of_nonneg_left scale (cp _)
  exact mul_le_mul head (prod_le_prod (fun j _=>cp j) (fun j _=>tail j))
    (prod_nonneg (fun j _=>cp j)) (bp i)

end YM.Integration.FVA1Physical.Marked.RemoteRoster
