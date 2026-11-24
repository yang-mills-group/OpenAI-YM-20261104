import YM.Integration.FVA1Physical.CommonHull.InteractingShortTerritoryInvoice

/-! Measurability of the field-chosen component and its exact signed crossing
on the full gas, including every quiet vacuum completion. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Marked.RemoteRoster
open Finset Set MeasureTheory Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Fusion.Attached Exchange Exchange.RoseCut
open scoped Classical BigOperators
variable {Y X:Type*}[Countable Y][MeasurableSpace X]

private def tier (edge:X→Y→Y→Prop)(x:Y):ℕ→Y→Set X
  | 0,y=>if x=y then Set.univ else ∅
  | k+1,y=>⋃z:Y,(tier edge x k z)∩{U|edge U z y}

private theorem reach_event (edge:X→Y→Y→Prop)(em:∀x y,MeasurableSet {U|edge U x y})(x y:Y):
    MeasurableSet {U|Relation.ReflTransGen (edge U) x y}:=by
  have tiered(k:ℕ)(z:Y):MeasurableSet (tier edge x k z):=by
    induction k generalizing z with
    | zero=>dsimp only [tier];split <;> simp
    | succ k ih=>exact MeasurableSet.iUnion fun a=>(ih a).inter (em ..)
  have eq:{U|Relation.ReflTransGen (edge U) x y}=⋃k:ℕ,tier edge x k y:=by
    ext U;constructor
    · intro h;change Relation.ReflTransGen (edge U) x y at h
      induction h with
      | refl=>exact Set.mem_iUnion.mpr ⟨0,by simp only [tier,if_true,Set.mem_univ]⟩
      | @tail z v chain step ih=>
        obtain ⟨k,ok⟩:=Set.mem_iUnion.mp ih
        exact Set.mem_iUnion.mpr ⟨k+1,Set.mem_iUnion.mpr ⟨z,ok,step⟩⟩
    intro h;obtain ⟨k,ok⟩:=Set.mem_iUnion.mp h
    clear h
    induction k generalizing y with
    | zero=>
      by_cases eq:x=y
      · exact eq ▸ Relation.ReflTransGen.refl
      simp only [tier,if_neg eq,Set.mem_empty_iff_false] at ok
    | succ k ih=>
      obtain ⟨z,seen,last⟩:=Set.mem_iUnion.mp ok
      exact (ih z seen).tail last
  rw [eq];exact MeasurableSet.iUnion fun k=>tiered k y

variable {G:Gauge}{n:Side}{V T I:Type}[DecidableEq V]{C:Census V}{o:V→Site n}{P:Rep G n}
  (A:Gallery T I o P C)(t:T)(D:ℕ)(x:Site n)

private theorem active_short (i:ℕ):Measurable fun U=>shortActors P.activities P.p (fun a=>A.K.hard t a U) D i:=by
  by_cases small:coverNumber P.p.B (P.activities.forced i).support≤D
  · simpa only [shortActors,if_pos small] using (A.K.locality t i).borel
  simp only [shortActors,if_neg small];exact measurable_const

theorem territory_site_borel (y:Site n):
    MeasurableSet {U:Config G n|y∈shortTerritory P.activities P.p (fun i=>A.K.hard t i U) x D}:=by
  let edge:=fun (U:Config G n)=>Edge P.activities (shortActors P.activities P.p (fun i=>A.K.hard t i U) D)
  have em (a b:Site n):MeasurableSet {U|edge U a b}:=by
    let pred:=fun i:ℕ=>a∈(P.activities.forced i).support ∧ b∈(P.activities.forced i).support
    let f:=fun i:ℕ=>fun U=>shortActors P.activities P.p (fun q=>A.K.hard t q U) D i
    have eq:{U|edge U a b}=⋃i:ℕ,if pred i then {U|f i U≠0} else ∅:=by
      ext U;constructor
      · rintro ⟨i,h,first,last⟩;exact Set.mem_iUnion.mpr ⟨i,by simpa only [if_pos (show pred i from ⟨first,last⟩),Set.mem_setOf_eq,f] using h⟩
      intro incl;obtain ⟨i,hit⟩:=Set.mem_iUnion.mp incl
      by_cases keep:pred i
      · exact ⟨i,by simpa only [if_pos keep,Set.mem_setOf_eq,f] using hit,keep⟩
      simp only [if_neg keep,Set.mem_empty_iff_false] at hit
    rw [eq];refine MeasurableSet.iUnion fun i=>?_
    by_cases keep:pred i
    · rw [if_pos keep];exact (measurableSet_eq_fun (active_short A t D i) measurable_const).compl
    rw [if_neg keep];exact MeasurableSet.empty
  simpa only [shortTerritory,mem_filter,Finset.mem_univ,true_and] using (reach_event edge em x y)

theorem territory_borel (K:Support n):
    MeasurableSet {U:Config G n|shortTerritory P.activities P.p (fun i=>A.K.hard t i U) x D=K}:=by
  let S:=fun U=>shortTerritory P.activities P.p (fun i=>A.K.hard t i U) x D
  have eq:{U|S U=K}=⋂ y:Site n,if y∈K then {U|y∈S U} else {U|y∈S U}ᶜ:=by
    ext U;constructor
    · intro h;change S U=K at h;apply Set.mem_iInter.mpr;intro y
      by_cases yes:y∈K <;> simp only [yes,if_true,if_false,Set.mem_setOf_eq,Set.mem_compl_iff,h,not_false_eq_true]
    intro h;apply Finset.ext;intro y;have member:=Set.mem_iInter.mp h y
    by_cases yes:y∈K
    · rw [if_pos yes] at member;exact ⟨fun _=>yes,fun _=>member⟩
    rw [if_neg yes] at member;exact ⟨fun owned=>(member owned).elim,fun k=>(yes k).elim⟩
  change MeasurableSet {U|S U=K};rw [eq];refine MeasurableSet.iInter fun y=>?_
  by_cases yes:y∈K
  · rw [if_pos yes];exact territory_site_borel A t D x y
  rw [if_neg yes];exact (territory_site_borel A t D x y).compl

end YM.Integration.FVA1Physical.Marked.RemoteRoster
