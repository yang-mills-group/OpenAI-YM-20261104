import YM.Integration.FVA1Physical.TwoReset.Letters
import YM.QuadraticLocal.Fk.Meet

/-! Mixing many finite sums of replicated rows (they may already be mixed
connected terms), with independent marks, but using the original Club geometry
on the physical stencil. Extends ScatterR.participates. -/
set_option autoImplicit false
set_option maxHeartbeats 750000
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.FVA1Physical.TwoReset.LinearLetters
open Function Filter Finset Lattice RG Precision Tree YM.Wilson QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Sunrise Comparison Comparison.RG02 Comparison.RG02.Bulk
open Next.SectorChange Marker Multi PertExtension.Series Extra.Trajectories
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {V ι μ α : Type} {G : Gauge} {n c f : Side}
variable [DecidableEq V]
variable (F : Finset ι) (P₁ : ℝ → Config G f → ℝ)
    (L : ι → ℝ → Config G f → ℂ) {J : Passport n V} {R : Census V}
    (M : ι → Row J R G α) (q : ι → ℂ) (w : V→ℕ)

variable {B : StepData c f} {P : Clip} {T : PathData G} {O : ChartRatio G}
variable (K : Kernel B P T O) (A : Forest B.ratio) (t : B.Choices)
    (x : Exterior.fieldDir G c 1) (r i : ℕ) (hi:i≤r)

variable [DecidableEq ι]

section
variable [Fintype μ] [DecidableEq μ] [Fintype ι] (u : μ ↪ ι)
local notation "X" => edition univ P₁ L (fun i=> (M i).lamp.toll)
local notation "X'" => edition univ P₁ (L ∘ u) (fun i=> (M (u i)).lamp.toll)

-- restrain Mark impulses to the incoming CLUB subset. No condition on roots or supports.
private lemma pin_mark : Comparison.RG02.Sources.pin (ScatterR.pouch u) X = X' := by
  let S := ScatterR.pouch u
  apply ScatterR.extC
  · funext U
    change (X).mark _ = (X').mark U
    let s := univ.filter (fun j:μ=> U.val = (Focus.detailI j).val)
    let v := univ.filter (fun i:ι=> S.share U.val=(Focus.detailI i).val)
    have e (j:μ) : S.share (Focus.detailI j).val = (Focus.detailI (u j)).val := S.fire _
    have h : s.image u = v := by
      ext i
      constructor
      · intro h
        obtain ⟨j,hj,rfl⟩ := mem_image.mp h
        exact mem_filter.mpr ⟨mem_univ _, Eq.trans (congr_arg _ (mem_filter.mp hj).2) (e j)⟩
      intro h
      obtain ⟨j,hj⟩:=U.prop
      have ht : S.share U.val = (Focus.detailI i).val := (mem_filter.mp h).2
      have hp : u j ∈ (S.share U.val).val := mem_image_of_mem _ hj
      rw [ht] at hp
      have h' : i = u j := (Finset.mem_singleton.mp hp).symm
      subst i
      exact mem_image.mpr ⟨j,mem_filter.mpr ⟨mem_univ _,S.inj (ht.trans (e j).symm)⟩,rfl⟩
    change ∑ j∈v, (1:ℂ) • L j = ∑ j∈s,(1:ℂ) • L (u j)
    rw [← h,sum_image u.injective.injOn]
  · exact funext fun j => congr_arg (·+1) (ScatterR.sieve M u (M ∘ u) rfl j.val)
  rfl

include hi
private lemma limit_edition (S : Finset μ) : (Order.observe _ r
    (Order.logMarked (Bulk.Fk K A t X x r)) i).part (Focus.onto (S.image u)) =
    (Order.observe _ r (Order.logMarked (Bulk.Fk K A t X' x r)) i).part (Focus.onto S) := by
  let P := ScatterR.pouch u
  change (P.restriction (Order.observe _ r (Order.logMarked (Bulk.Fk K A t X x r)) i)).part (Focus.onto S) = _
  rw [← pin_mark P₁ L M u]
  let Z := Bulk.Fk K A t X x r
  let o := Embedding.refl (Fin r)
  let p := Order.truncate P o
  have he : p Z = Bulk.Fk K A t (Comparison.RG02.Sources.pin P X) x r := Comparison.RG02.Sources.criterion ..
  rw [← he, ← Comparison.RG02.Sources.trunc_marked P o (fk_unit ..),
    Order.trunc_observe P o (Order.sym_logMarked (fk_unit ..) (fk_sym ..)) hi]
end

section
variable [Fintype V]
local notation "seats" => Focus.census ↥F
local notation "lit" => edition (Finset.univ:Finset ↥F) P₁ (L ∘ Subtype.val)
  (fun k:↥F=> (M k.val).lamp.toll)
local notation "actor" => ScatterR.actor M
local notation "wt" => (fun i:Multi.Hot R => Launch.index R w i.val+1)
local notation "wa" => colors F P₁ L R (ScatterR.actor M) q wt

/-- One response per incoming club. -/
noncomputable def mixedTerm (C : Club M) : Poly R := Poly.send (Club.alliance M C)
  ((Order.observe _ r (Order.logMarked (Bulk.Fk K A t (edition univ P₁ (L ∘ (Club.stamp M C))
    (fun i=> (Club.troops M C i).lamp.toll)) x r)) i).part (Focus.onto
      (univ:Finset (Club.Keys M C))) * ∏ j ∈ C.val, q j)

omit [Fintype V] [DecidableEq ι] in
private lemma subtype_colors : colors F P₁ L R (actor) q wt =
    colors (Finset.univ:Finset ↥F) P₁ (L ∘ Subtype.val) R (actor ∘ Subtype.val) (q∘Subtype.val) wt := by
  apply ScatterR.extC
  · funext j
    unfold colors
    simp_rw [Finset.sum_filter,Function.comp_apply]
    exact (Finset.sum_attach F (fun i:ι=> if j.val=(ScatterR.actor M i).val then q i • L i else 0)).symm
  · rfl
  rfl

include hi
set_option quotPrecheck false
theorem mix_clubs (H : ∀i∈F, (M i).lamp.toll=Launch.index R w (M i).mode)
    (hv : ∀i∈F, ¬(M i).clear)
    (hc : ∀ i∈F, ContDiffAt ℝ ω (Bulk.posed B A (L i)) 0) :
    Order.observe R r (Order.logMarked (Bulk.Fk K A t wa x r)) i =
      ∑ j∈ScatterR.lounge M F, mixedTerm P₁ L M q K A t x r i j := by
  rw [subtype_colors F P₁ L M q w]
  let l := L ∘ (Subtype.val:↥F→ι)
  have hd : ∀ j:↥F,j∈univ→ ContDiffAt ℝ ω (Bulk.posed B A (l j)) 0:= fun j _=>hc _ j.prop
  rw [finite_mixing (univ:Finset ↥F) P₁ l R (actor∘Subtype.val) (q∘Subtype.val) _ K A t
    hd (fun j=> (M j.val).lamp.toll) (fun j _=> congr_arg (·+1) (H j.val j.prop).symm) x r i,
    TableMap.pushes]
  let Q := Bulk.Fk K A t lit x r
  let W₁ := Order.logMarked Q
  let f₀ := Order.observe seats r W₁ i
  have z : f₀.part (Focus.onto (∅:Finset ↥F))=0 := by
    have he : Order.observe seats r (0:_ ) i=0:= (Order.observeL (R:=seats) (r:=r) i).map_zero
    have h : Order.blanked seats f₀=0:= (Order.observe_bottom W₁ i).symm.trans
      ((congr_arg (fun x=>Order.observe seats r x i) (Order.log_marked (fk_unit ..))).trans he)
    change f₀.part _=0
    have hq:= Order.pure_marks f₀ (seats).quiet
    rw [if_pos rfl,h] at hq
    exact hq.symm
  let p (v:Club M) := Finset.preimage v.val (Subtype.val : ↥F→ι) Subtype.val_injective.injOn
  let We := ScatterR.lounge M F
  let Lx (j:ι) := Poly.send (M j).mode (q j)
  have hV (c:Club M) (hv:c∈We) : (p c).image Subtype.val = c.val := by
    unfold p
    rw [image_preimage]
    apply filter_true_of_mem
    intro i h
    exact ⟨(⟨i,Finset.mem_powerset.mp (Finset.mem_preimage.mp hv) h⟩:↥F),rfl⟩
  let projected := image (Subtype.val:↥F→ι)
  have hp : Injective projected := Finset.image_injective Subtype.val_injective
  have HJ (c:Club M) : c∈We → ∀ i∈c.val, i∈F:= fun h j hj=> Finset.mem_powerset.mp (Finset.mem_preimage.mp h) hj
  let g (u':Finset ↥F) := (f₀.part (Focus.onto u')) • ∏ j∈u', Lx j.val
  change ∑ i':Finset ↥F, g i' = _
  calc
    _ = ∑ i'∈We.image p,g i' := by
      symm
      apply Finset.sum_subset (subset_univ _)
      intro i' _ hh
      rcases Finset.eq_empty_or_nonempty i' with hz|hx
      · unfold g; rw [hz,z,zero_smul]
      let s := projected i'
      have hS (i) (h:i∈s) : i∈F := by
        obtain ⟨k,hk,rfl⟩:= mem_image.mp h
        exact k.prop
      have omit_ : ¬∃ C:Club M,C.val=s:= by
        rintro ⟨j,h⟩
        have he : j∈ We:= mem_preimage.mpr (mem_powerset.mpr (fun j hx=> hS j (by rwa [← h])))
        exact hh (mem_image.mpr ⟨j,he,hp ((hV j he).trans h)⟩)
      unfold g
      have hQ : ∏ j∈i', Lx j.val = 0 := (prod_image (f:=Lx) (s:=i') Subtype.val_injective.injOn).symm.trans
        (Game.omitted M s q (hx.image Subtype.val) (fun i hi=>hv i (hS _ hi)) omit_)
      rw [hQ,smul_zero]
    _ = _ := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro i' h
        let u : Club.Keys M i' ↪ ↥F :=
          ⟨fun k=>⟨Club.stamp M i' k, HJ i' h _ (Club.attends ..)⟩,
          fun j k he=> Club.troop_inj M i' (congr_arg (Subtype.val:↥F→ι) he)⟩
        have hU : p i' = Finset.univ.image u := by
          apply hp
          change (p i').image Subtype.val = Finset.image Subtype.val _
          rw [hV i' h,image_image]
          ext1 j; simp only [mem_image,mem_univ,true_and]
          exact ⟨fun hv=> Club.attends_rev M i' j hv,fun ⟨a,ha⟩=> ha ▸ Club.attends M i' a⟩
        let val := ((Order.observe _ r (Order.logMarked (Bulk.Fk K A t (edition univ P₁ (l ∘ u)
          (fun j=> (M (u j).val).lamp.toll)) x r)) i).part (Focus.onto (univ:Finset (Club.Keys M i'))))
        have hW : f₀.part (Focus.onto (p i')) = val := by
          rw [hU]
          exact limit_edition P₁ l (M ∘ (Subtype.val:↥F→ι)) K A t x r i hi u univ
        have hQ : (∏ j∈p i', Lx j.val) = ∏ j∈i'.val, Poly.send (M j).mode (q j) :=
          (prod_image (f:=Lx) (s:=p i') Subtype.val_injective.injOn).symm.trans
            (congr_arg (fun s:Finset ι=> ∏ i∈s,Lx i) (hV i' h))
        unfold g
        rw [hQ,hW,Game.club_price]
        exact (send_scale ..).symm
      exact fun i hi j hj he=> Subtype.ext ((hV i hi).symm.trans
        ((congr_arg projected he).trans (hV j hj)))

end
end YM.Integration.FVA1Physical.TwoReset.LinearLetters
