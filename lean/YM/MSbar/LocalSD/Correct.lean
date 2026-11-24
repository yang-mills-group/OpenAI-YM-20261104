import YM.MSbar.LocalSD.Recenter
/-! # Density correction formula. No charge on vac sectors disjoint but
allow all the merged partners. Identity at actual flags, before Grassmann. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Bulk.Recenter
open Lattice Wilson RG Filter Function MeasureTheory PhysicalNext.Repeat.Lotus
open Push Finset Push.AbsoluteSums
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{c f:Side}{S:StepData c f}{R:Rep G f}
variable {a σ C δ Λ w:ℝ} {κ: Config G f→ Config G f} {g:Config G f→ℝ}
variable (X: Support f) (T:Tracks R X κ g S a) (U:Config G f)
   (h:R.Lawful σ C Λ δ w)(K:MergeProof.Menu.Arsenal R)
set_option quotPrecheck false
local notation "F!"=> flags R.p.threshold U
local notation "E!"=> R.activities
variable {X}
private lemma merge_two (p:Chunk R X) (y:Finset ℕ)(P : ∀ i∈y,Disjoint (extent X p) (need R i)) : Disjoint p.val y ∧ tag K p ∉ y ∧
    (R.activities.admissible R.p U (p.val ∪ y) ↔ R.activities.admissible R.p U (insert (tag K p) y)):=by
    let z:= tag K p; have hp (i) (hi:i∈p.val): need R i⊆ extent X p := (subset_biUnion_of_mem _ hi).trans subset_union_right
    have hh : Disjoint p.val y := Finset.disjoint_left.mpr fun i hi hv=> by
       obtain ⟨t,ht⟩:=(R.activities.forced i).inventory_ne; have he: t∈ need R i :=(R.activities.forced i).inventory_sup ht; exact Finset.disjoint_left.mp (P _ hv) (hp i hi he) he
    have hz : z∉y:=by
       intro e; obtain ⟨v,hv⟩:=p.prop.1; obtain ⟨q,hq⟩:= (R.activities.forced v).inventory_ne; have hJ:=hp v hv ((R.activities.forced v).inventory_sup hq); exact Finset.disjoint_left.mp (P _ e) hJ ((chosen K p).1.symm ▸ hJ)
    refine ⟨hh,hz,?_⟩
    have he : ((insert z y).biUnion (seen R))=(p.val∪y).biUnion (seen R):=by rw [biUnion_insert,union_biUnion]; exact congr_arg (_∪ ·) rfl |>.trans (congr_arg (· ∪ y.biUnion (seen R)) (chosen K p).2.1)
    constructor
    · rintro ⟨ha,hb⟩; refine ⟨?_,he.trans hb⟩
      have hQ (i)(hi:i∈y):Disjoint (need R z) (need R i):=by rw [show need R z=extent X p from (chosen K p).1]; exact P i hi
      rintro i hi j hj hN; rcases mem_insert.mp hi with rfl|ht
      · rcases mem_insert.mp hj with H|hb; exact (hN H.symm).elim; exact hQ _ hb
      rcases mem_insert.mp hj with rfl|hu; exact (hQ _ ht).symm; exact ha (mem_union_right _ ht) (mem_union_right _ hu) hN
    rintro ⟨ha,hb⟩; refine ⟨?_,he.symm.trans hb⟩
    rintro i hi j hj hN; rcases mem_union.mp hi with hi|hi <;> rcases mem_union.mp hj with hj|hj
    exact p.prop.2.2 hi hj hN; exact (P j hj).mono_left (hp i hi); exact (P i hi).symm.mono_right (hp j hj); exact ha (mem_insert_of_mem hi) (mem_insert_of_mem hj) hN
private def box (U:Config G f)(p:Finset ℕ) (κ: Config G f→ Config G f) : ℝ:=R.activities.gasOccurrence R.p p (κ U)-R.activities.gasOccurrence R.p p U
variable (b:ℕ→ℝ)(hg:∀ i,0 ≤ b i ∧ ∀ U,‖R.activities.K i U‖ ≤ b i)
local notation "b0"=> pay T h K b hg
variable (p : Chunk R X)
include h T
lemma together (hT:g U≠0) (y:Finset ℕ) (he:∀ i∈y,Disjoint (extent X p) (need R i)) : g U*box (R:=R) U (p.val ∪ y) κ=(b0 p).bun (insert (tag K p) y) U:=by
    obtain ⟨hS,hz,hQ⟩ := merge_two U K p y he
    have hf:=T.paid U hT
    have ht : R.activities.admissible R.p (κ U) (p.val∪y) ↔R.activities.admissible R.p U (p.val ∪ y):=by unfold Activities.admissible; rw [hf]
    unfold Fibre.bun box Activities.gasOccurrence; simp_rw [ht,hQ]
    split
    next ha =>
      have hO i (hi:i∈y):R.activities.K i (κ U)= R.activities.K i U:= ((h.labels.forced.reads i) _ _ (T.localOp (need R i) U hT ((he i hi).mono_left subset_union_left)) (by rw [hf])).symm
      have hp : extent X p ∩ flags R.p.threshold U=lore X p:=by
          ext t; rw [← (hQ.mpr ha).2,Finset.union_biUnion]; constructor
          · intro hi
            obtain ⟨ht,hu⟩:= mem_inter.mp hi; rcases Finset.mem_union.mp hu with hl|hy; exact hl
            obtain ⟨i,hi,hf⟩:= mem_biUnion.mp hy; exact (disjoint_left.mp (he i hi) ht ((R.activities.forced i).inventory_sup hf)).elim
          intro hj; exact mem_inter.mpr ⟨(sure p).2 hj, mem_union_left _ hj⟩
      unfold Fibre.bill; rw [if_pos (show (b0 p).turn.Occupied _ from mem_insert_self ..)]; change _=toll κ g p U*∏ i∈_,R.activities.K i U
      unfold toll; rw [if_pos hp,prod_union hS,prod_union hS, show ∏ i∈y,R.activities.K i (κ U)=_ from prod_congr rfl hO]; simp only [pay, Wing.remaining, erase_insert hz]; ring
    next h=> ring
def tails (p:Chunk R X): Set (Finset ℕ):= {y |∀ i∈y,Disjoint (extent X p) (need R i)}
def floral (x : Σ p:Chunk R X,Subtype (tails p)) := x.1.val ∪ x.2.val
local notation "ξ" => Σ p:Chunk R X,Subtype (tails p)
omit h T in
lemma floral_inj : Injective (floral (R:=R) (X:=X)):=by
    rintro ⟨p,y⟩ ⟨q,z⟩ e; simp only [floral] at e
    have hi (p q:Chunk R X)(y: Subtype (tails p))(z: Subtype (tails q))(h:p.val∪y.val=q.val∪z.val): p.val ⊆ q.val:=by
       intro i hv; rcases mem_union.mp (h ▸ mem_union_left y.val hv) with hl|hk; exact hl
       exact (p.prop.2.1 _ hv ((z.prop i hk).mono_left subset_union_left)).elim
    have hs : p=q := Subtype.ext (Finset.Subset.antisymm (hi p q y z e) (hi q p z y e.symm)); subst q
    have hy(z y:Subtype (tails p))(h:p.val∪ y.val=p.val∪z.val):y.val⊆z.val:=by
       intro i hv; rcases mem_union.mp (h ▸ mem_union_right p.val hv) with ht|hh; exact (p.prop.2.1 i ht ((y.prop i hv).mono_left subset_union_left)).elim; exact hh
    rw [show y=z from Subtype.ext (Finset.Subset.antisymm (hy z y e) (hy y z e.symm))]

lemma flower (hT:g U≠0) (l: Finset ℕ) (hv : box (R:=R) U l κ≠0) : ∃ x:Σ p:Chunk R X,Subtype (tails p),floral x=l:=by
   have hk:= T.paid U hT
   unfold box Activities.gasOccurrence at hv; simp_rw [show R.activities.admissible R.p (κ U) l↔ R.activities.admissible R.p U l from (by unfold Activities.admissible; rw [hk])] at hv; split at hv
   swap; · exact (hv (sub_zero ..)).elim
   next hu =>
   let t:=l.filter (fun i=> ¬Disjoint X (need R i))
   have hb:t⊆l:=filter_subset ..
   have ht : t.Nonempty:=by
      by_contra! ht; refine hv (sub_eq_zero.mpr (prod_congr rfl (fun i hi=> ?_)))
      refine (h.labels.forced.reads i _ _ (T.localOp (need R i) _ hT ?_) (by rw [hk])).symm
      exact by_contra fun hh=> notMem_empty i (ht ▸ (show i∈t from mem_filter.mpr ⟨hi,hh⟩))
   let p:Chunk R X:=⟨t,ht,fun i hi=> (mem_filter.mp hi).2, hu.1.mono (coe_subset.mpr hb)⟩
   refine ⟨⟨p,l\t,?_⟩, union_sdiff_of_subset hb⟩
   intro i hi
   obtain ⟨hi,hb⟩:=mem_sdiff.mp hi; refine disjoint_union_left.mpr ⟨?_,?_⟩
   · exact by_contra fun h=> hb (mem_filter.mpr ⟨hi,h⟩)
   apply disjoint_left.mpr; intro v hv hz; obtain ⟨j,hj,hp⟩:= mem_biUnion.mp hv
   exact disjoint_left.mp (hu.1 (mem_of_mem_filter j hj) hi (fun e=> hb (e ▸ hj))) hp hz

lemma bun_tail (hT:g U≠0) (l: Finset ℕ) (hu:(b0 p).bun l U ≠ 0) : ∃ y:Subtype (tails p), insert (tag K p) y.val=l:=by
   let z:= tag K p; unfold Fibre.bun Fibre.bill at hu; split at hu
   swap; · exact (hu rfl).elim
   next hp =>
   split at hu
   next hf =>
     have ht:z∈l:=hf; refine ⟨⟨l.erase z,?_⟩, Finset.insert_erase ht⟩
     intro i hi; rw [← (chosen K p).1]; exact hp.1 ht (mem_of_mem_erase hi) (ne_of_mem_erase hi).symm
   next h=> exact (hu rfl).elim

lemma flowers (K : MergeProof.Menu.Arsenal R): HasSum (fun p:Chunk R X=> (pay T h K b hg p).cicada U) (g U*(R.eval (κ U)*Real.exp (R.exponent U-R.exponent (κ U))- R.eval U)):=by
    by_cases he:g U=0
    · have hb(p:Chunk R X)(k:Finset ℕ) : (pay T h K b hg p).bun k U=0:=by
          unfold Fibre.bun Fibre.bill; split_ifs; next h'=> change toll κ g p U*_=0; simp only [toll,he,zero_mul,ite_self]
          all_goals rfl
      simp_rw [Fibre.cicada,hb,tsum_zero,mul_zero,he, zero_mul]; exact hasSum_zero
    let E:=R.activities;let A:=Real.exp (R.exponent U); let v(i:Finset ℕ):= A*(g U*box (R:=R) U i κ)
    let J:=g U*(R.eval (κ U)*Real.exp (R.exponent U-R.exponent (κ U))- R.eval U)
    have hZ : HasSum v J:=by
       let g' := R.p; have ht(U : Config G f): HasSum (fun i=> R.activities.gasOccurrence R.p i U) (R.activities.gas R.p U):= ((R.activities.gasSeries h.labels).summable U).hasSum -- error theorem
       convert! ((((ht (κ U)).sub (ht U)).mul_left (g U)).mul_left A) using 1; unfold A J Rep.eval; rw [Real.exp_sub]; field_simp
    have hp:= ((floral_inj (R:=R) (X:=X)).hasSum_iff (f:=v) (fun i hn=> by_contra (fun hv=>hn (flower T U h he i (right_ne_zero_of_mul (right_ne_zero_of_mul hv)))))).2 hZ
    refine HasSum.sigma hp fun i=> ?_
    let w(y:Subtype (tails i)):= insert (tag K i) y.val; have heq(y:Subtype (tails i)): (v∘floral) ⟨i,y⟩= A*(pay T h K b hg i).bun (w y) U:=congr_arg (A*·) (together T U h K b hg i he _ y.prop)
    have hw:Injective w:=by
       intro a b hA
       have ha:= (merge_two U K i a.val a.prop).2.1; have hb:= (merge_two U K i b.val b.prop).2.1
       refine Subtype.ext ?_; exact (erase_insert ha).symm.trans ((congr_arg (·.erase (tag K i)) hA).trans (erase_insert hb))
    have hu:= ((pay T h K b hg i).bud h).summable U; simp_rw [heq]
    exact ((hw.hasSum_iff (f:=fun j=> (pay T h K b hg i).bun j U) (fun l hb=>by_contra (fun hh=>hb (bun_tail T U h K b hg i he l hh)))).2 hu.hasSum).mul_left A
end YM.MSbar.Bulk.Recenter
