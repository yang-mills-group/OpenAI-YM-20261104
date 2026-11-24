import YM.Integration.WilsonCumulantRelocation

/-! At two independently fixed marked sites the disconnected term cancels
exactly. Only the relative child offset enters, against the held actual
microscopic Wilson observable, on the one normalized original law. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredRelativePair
open Function Finset MeasureTheory Lattice Wilson RG Source Marker Multi Extraction
open Extra.Trajectories WilsonReportMomentDifference WilsonReportCashierConnected
open Primitives.GCC.Anchor Comparison.RG02.Cumulants WilsonCumulantCommonOffset
open scoped Classical BigOperators

theorem leading {V : Type} [Fintype V] [DecidableEq V] {Γ : Census V} (A B : Marker.Poly Γ)
    (a₀ : A.part Γ.quiet=1) (b₀ : B.part Γ.quiet=1) (s : Multi.Hot Γ)
    (below : ∀ z : Γ.Mode, z.val ⊂ s.val.val → A.part z=B.part z) :
    (connected A).part s.val-(connected B).part s.val=A.part s.val-B.part s.val := by
  let one := (parts Γ).fire s
  have use : one ∈ shards Γ s.val := by simp [one,shards]
  rw [log_partition A a₀,log_partition B b₀,←sum_sub_distrib]
  refine (sum_eq_single_of_mem one use ?_).trans ?_
  · intro t ht hne
    have subset (z : Multi.Hot Γ) (hz : z∈t.val) : z.val.val⊆s.val.val := by
      have uni := (mem_filter.mp ht).2
      intro i hi; rw [←uni]; exact mem_biUnion.mpr ⟨z,hz,hi⟩
    have away : s∉t.val := by
      intro hs; apply hne; apply Subtype.ext; ext z
      change z∈t.val ↔ z∈({s} : Finset (Multi.Hot Γ)); rw [mem_singleton]
      constructor
      · intro hz; by_contra off; obtain ⟨i,hi⟩ := z.property
        exact disjoint_left.mp (parts_wise t hz hs off) hi (subset z hz hi)
      · rintro rfl; exact hs
    have same : (∏ z∈t.val,A.part z.val)=(∏ z∈t.val,B.part z.val) := by
      apply prod_congr rfl; intro z hz; apply below
      exact (Finset.ssubset_iff_subset_ne.mpr ⟨subset z hz,fun h => away (Multi.Hot.eq_of_sites h ▸ hz)⟩)
    rw [same,sub_self]
  · simp [one,Census.fire,mobiusTop]

variable {G : Gauge} {C : Family G} {n N p k : ℕ}

private theorem single (Γ : Census (Fin n)) (d : Fin n→ℕ) (v : (i:Fin n)→C.label (d i))
    (a b : Fin n→Site (C.side N p)) (s : Γ.Mode) (h : s.val.card≤1) :
    (microscopic Γ C (fun i=>C.O N p (v i) (a i))).part s=
      (microscopic Γ C (fun i=>C.O N p (v i) (b i))).part s := by
  by_cases empty : s.val=∅
  · change moment _ (fun U=>∏ i∈s.val,C.O N p (v i) (a i) U)=moment _ (fun U=>∏ i∈s.val,C.O N p (v i) (b i) U)
    simp [empty]
  obtain ⟨i,only⟩ := card_eq_one.mp (le_antisymm h (card_pos.mpr (nonempty_iff_ne_empty.mpr empty)))
  let q := a i-b i
  have e := congrArg (fun X : Marker.Poly Γ => X.part s) (moments (C:=C) (N:=N) (p:=p) Γ d v b q)
  change moment _ (fun U=>∏ j∈s.val,C.O N p (v j) (b j+q) U)=moment _ (fun U=>∏ j∈s.val,C.O N p (v j) (b j) U) at e
  change moment _ (fun U=>∏ j∈s.val,C.O N p (v j) (a j) U)=moment _ (fun U=>∏ j∈s.val,C.O N p (v j) (b j) U)
  have adj : b i+q=a i := by dsimp [q]; abel
  simpa only [only,prod_singleton,adj] using e

theorem held (Γ : Census (Fin n)) (hk : k≤N) (d : Fin n→ℕ) (v : (i:Fin n)→C.label (d i))
    (y : Fin n→Site (C.side N p)) (i j : Fin n) (ij : i≠j) (s : Γ.Mode) (hs : s.val={i,j}) :
    let b := anchored (C:=C) (N:=N) (p:=p) hk y
    displaced Γ hk d v y s = moment (C.beta N p) (fun U => C.O N p (v i) (b i) U *
       (C.O N p (v j) (y j-(y i-b i)) U-C.O N p (v j) (b j) U)) := by
  let b := anchored (C:=C) (N:=N) (p:=p) hk y
  let a := fun t => y t-(y i-b i)
  let F := fun t => C.O N p (v t) (a t); let E := fun t => C.O N p (v t) (b t)
  let A := microscopic Γ C F; let B := microscopic Γ C E
  have unit (Z : Fin n → Config G (C.side N p)→ℂ) : (microscopic Γ C Z).part Γ.quiet=1 := by
    change moment _ (fun U => ∏ t∈(∅ : Finset (Fin n)),Z t U)=1; simp [moment]
  have cr : s.val.card=2 := by rw [hs]; simp [ij]
  have nz : s.val.Nonempty := card_pos.mp (by omega)
  have low (t : Γ.Mode) (ht : t.val ⊂ s.val) := single (C:=C) (N:=N) (p:=p) Γ d v a b t (by have := card_lt_card ht; omega)
  have same := relative (C:=C) (N:=N) (p:=p) Γ hk d v y (y i-b i) s
  calc
    _ = (connected A).part s-(connected B).part s := same
    _ = A.part s-B.part s := leading A B (unit _) (unit _) ⟨s,nz⟩ low
    _ = WilsonCumulantRelocation.movedMoment F E s.val :=
      (WilsonCumulantRelocation.one_block F E (fun t=>C.continuousO ..) (fun t=>C.continuousO ..) _).symm
    _ = _ := by
      apply congrArg (moment (C.beta N p)); funext U
      have ai : a i = b i := by dsimp [a]; abel
      simp only [WilsonCumulantRelocation.difference,prod_map_toList,hs,prod_insert (notMem_singleton.mpr ij),prod_singleton,F,E,ai]
      ring

end YM.Integration.WilsonMeasuredRelativePair
