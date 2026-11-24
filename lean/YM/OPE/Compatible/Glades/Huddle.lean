import YM.OPE.Compatible.Glades.TimeMap
/-! Supply time map facts at actual quota.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars true
noncomputable section
namespace YM.OPE.Arboreal.CutOrder
open Function Filter Lattice RG Wilson MergeProof Source Accent Spec Ribbons
open PhysicalNext.Repeat.Legato Bandage Ribbons.ManyCopies Ribbons.ManyCopies.Stem MergeProof.Float
open Push Marker Local Extra.Histories Extra.Trajectories MeasureTheory Extra.Multi Finset
open scoped Topology Classical
variable {X V:Type}[PartialOrder X][OrderBot X][Fintype X]
    (D:Origin X) {U Q:Finset X}{m j:X→ℕ}
open YM.OPE.Allot Series Lights
variable {G:Gauge}{C:Family G} (A:Allot C){P: Ensemble V}{l:ℕ→ℕ}
variable {N p b n:ℕ} {E:Track C.path V p}{o:X→Track C.path V p}
variable (h:CutOrder C P D U m j N p E o b l)(S:Series Q m)(hU:Q⊆U)
set_option quotPrecheck false
local notation "i"=> whenHigh Q m
local notation "F"=> crease D S
local notation "o₀" => fun x:brim D Q=>o x.val
local notation "o₁" => fun x:after D Q m=>o x.val
local notation "k"=>fun u=>finishAt D m u
include hU S
lemma kids_at (hx:∀ x∈brim D Q, i ≤ roof U m N x)(u:after D Q m): i≤ roof U m N u.val:=by
    by_cases he:u.val∈Q
    · have H : m u.val=i:= birth_stamp D S (mem_inter.mpr ⟨u.2,he⟩); exact le_of_eq (H.symm.trans (if_pos (hU he)|>.symm))
    exact hx _ (spec D S u.2 he)
lemma afterUp (u:after D Q m): u.val ∈ allUp D U:=by
   by_cases hv:u.val∈Q
   · exact mem_union_left _ (hU hv)
   exact brim_under D U Q hU (spec D S u.2 hv)
include h
lemma bound (hx:∀ x∈ brim D Q, i ≤ roof U m N x): Bind C P E F (o₀) (o₁) i (fun u=>finishAt D m u.val) (fun u=>finishAt D m u.val) (fun u=>j u.val):=by
    refine ⟨fun x=> high D S ((on_brim D Q).mp x.2|>.2.2),fun a he=>?_,fun x he=> lt_of_lt_of_le h.head (lower_earliest D U m h.plan _ (afterUp D S hU x)),fun x he=>?_,fun x he=>?_,fun x _ b hb hk=> h.pare x.val (afterUp D S hU x) b hb (hk.trans_le (kids_at D S hU hx x)),fun x _=>?_,fun x v hv hw=>h.echo x.val (afterUp D S hU x) v hv (hw.trans (kids_at D S hU hx x)),fun x ht=> stamp_in D S x ht⟩
    · obtain ⟨x,hx,hQ⟩:= Series.same D S a he; exact ⟨x,hx,hQ ▸ rfl,hQ ▸ rfl⟩ -- orientation
    · have hh:= high_node D S x he; obtain ⟨ha,hb⟩:= h.epochs _ (hU (mem_inter.mp hh|>.2)); exact ⟨ha,hb.trans_eq (birth_stamp D S hh)⟩
    · have hh:=high_node D S x he
      -- rewrite offspring's stamp time
      exact birth_stamp D S hh ▸ h.inHost x.val (hU (mem_inter.mp hh|>.2))
    refine ⟨fun t ht ht'=> h.moves.mare t ((lower_earliest D U m h.plan x.val (afterUp D S hU x)).trans ht) ?_⟩; exact ht'.trans_le ((Finset.sup_mono hU).trans h.next.le)
omit h hU S
variable [Fintype V][DecidableEq V]
omit [DecidableEq V] in
lemma copies_dom {n:Side}{I:Type}[Fintype I](x:V×I→Site n)(M:ℕ)(h:Fintype.card I≤ M)(hi:∀ t:I,Injective (fun v=>x (v,t))):Occupancy x M:=by
   intro y; let S:= (univ: Finset (V×I)).filter (fun t=>x t=y); have he:Set.InjOn (Prod.snd (α:=V) (β:=I)) ↑S:=by
       rintro ⟨t,j⟩ hj ⟨t',j'⟩ hj' rfl; rw [(hi j) ((mem_filter.mp hj|>.2).trans (mem_filter.mp hj'|>.2).symm)]
   exact (card_image_of_injOn he).symm.le.trans ((Finset.card_le_univ _).trans h)
include h hU S
omit [DecidableEq V] in
lemma count_left [DecidableEq V] (hx:∀ x∈brim D Q,n ≤ roof U m N x)(hi: i ≤ n){t:ℕ}(ht:places X ≤ A.r t): Occupancy (Lights.pegs V ↥(brim D Q) (o₀) n) (A.r t):=by
   have hp:= h.plan; refine copies_dom _ _ ?_ fun x=> h.copies x.val (brim_under D _ _ hU x.2) n ((high D S ((on_brim D Q).mp x.2|>.2.2)).trans hi) (hx x.val x.2)
   rw [Fintype.card_coe]; exact le_trans (le_trans (Nat.le_add_right _ 0) (places_dom (X:=X) (brim D Q) (∅) |> (fun g=> by simpa using g))) ht
lemma incoming (hx:∀ x∈brim D Q,i+1≤ roof U m N x)(ht:places X ≤ A.r i): Incoming A F (o₀) (o₁) i (places X) (l i):=by
   let I:= whenHigh Q m; have hp : (Fintype.card ((brim D Q)⊕(buds D Q m)))≤ places X:=by simp only [Fintype.card_sum,Fintype.card_coe]; exact places_dom ..
   have hx₀ (x : after D Q m): I ≤ roof U m N x.val:=kids_at D S hU (fun x hp=>(Nat.le_succ _).trans (hx x hp)) x
   have he(z: buds D Q m): ((F).bunch (Sum.inr z)).val = z.val:=rfl -- precedence
   have hE(x:after D Q m): (k) x.val ≤ I :=by
       by_cases hf:x.val∈Q
       · exact high D S (S.base.roots (par_le ..) hf)
       exact high D S ((on_brim ..).mp (spec D S x.2 hf)|>.2.2)
   have hX(x:brim D Q): (k) x.val ≤ I:=high D S ((on_brim ..).mp x.2|>.2.2)
   have h_f(x:Site (C.path.S.side I p)):coverNumber (bins C I).B ({x,x}:Support _)≤ l I:=by
        obtain ⟨y,hy,hY⟩:= exists_mem_eq_sup Q (S.begun D) m; have hw:= h.costL y (hU hy); change I=_ at hY; have hc:1≤ l I:= hY ▸ hw
        have ht:= (bins C I).B_pos; simp only [Finset.insert_eq_of_mem (s:={x}) (mem_singleton_self _)]; exact (le_trans ((Corona.cover_mono (halo_subset 0 {x}) _).trans (show coverNumber (bins C I).B (Lattice.halo 0 {x}) ≤1 from by simpa using Lattice.Corona.tile x 0 (bins C I).B ht)) hc)
   refine ⟨fun x=>?_,count_left D A h S hU hx (Nat.le_succ _) ht, count_left D A h S hU (fun x hX=> (Nat.le_succ _).trans (hx x hX)) le_rfl ht,copies_dom _ _ (hp.trans ht) (fun i' => ?_),fun x v=>?_,hp,places_pos X⟩
   · by_cases hv:x.val ∈ Q
     · have he : (F).twig x= .inr ⟨x.val,mem_inter.mpr ⟨x.2,hv⟩⟩:= dif_pos hv; rw [he]; rfl
     obtain ⟨a,hH,hT⟩:=Series.same D S x ((cred D S x).mpr hv); rw [hH]; exact congr_arg (fun u=> o u I) hT
   · cases i'
     next x=> exact h.copies _ (brim_under D U Q hU x.2) I (hX x) (by specialize hx x x.2; omega) -- Nat.lt? ensure n exact p.
     next x=>
        let y:= (crease D S).bunch (.inr x); exact h.copies _ (afterUp D S hU y) _ (hE y) (hx₀ y)
   cases x
   next x=>
      let y:= (crease D S).bunch (.inl x)
      change coverNumber (bins C I).B ({o y.val I v,o x.val I v}:Support _) ≤ l I
      by_cases hm:(crease D S).SingleFiber y
      · obtain ⟨a,ha,hF⟩:=Series.same D S y hm; have h : a=x:= Sum.inl.inj (ha.symm.trans (((crease D S).sola y hm (.inl x)).mp rfl).symm); rw [show y.val=x.val from hF.symm.trans (h ▸ rfl)]; exact h_f _
      have hf:= high_node D S y hm; have hs:m y.val=I:= birth_stamp D S hf
      exact hs ▸ h.project _ x.val (hU (mem_inter.mp hf|>.2)) (brim_under D U Q hU x.2) (reaches D S x) ((stamp_in D S x hm).trans hs.symm) v
   next x=> exact h_f _
end YM.OPE.Arboreal.CutOrder
