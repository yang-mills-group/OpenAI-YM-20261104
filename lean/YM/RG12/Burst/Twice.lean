import YM.RG12.Burst.Birch
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mercury.Debonaire
import YM.RG12.Burst.Feder
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Blush
open Function Filter Lattice RG Wilson Finset MeasureTheory
open Push Push.AbsoluteSums Gas Ovens ConnectedActivityE6 Daisy Daisy.Charity Mallow Lotus
open PowerSeries Extra.Histories Progress.DirectedRecipe Next.Foundations Precision
open Blaze Blaze.March Poll Pond Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{c f n: Side}
variable {i j:ℕ} {o: Site n}{S:Support n}{B : BudgetPoint}
open Pressure Push.SectorMeasure Greenbelt Refrain
variable {S:StepData c f}{T: Tube G S}{L:Side}{P:Teller G} {Q: ConnectedActivityE6.Target G P}{W x μ C : ℝ}{o':Target.Order G W}{R:RG.Rep G f}
variable (H:Cash W x μ L Q o' C T R) (r : Cloud R) (o : Site c)
local notation "hd"=> r.live
local notation "hd'"=> r.pale
local notation "χ"=> Chi.canonical
variable (K R' : ℝ → Code G c)
variable (v: ℂ)
variable (F : YM.Labels.Frame G j)
section prices
local notation "M" => Blush.screen H r K R' v F
variable {R2 : Rep G c} (he:R2.p=B)
variable {A b q t d Y f₀ α k β e w t':ℝ}{n' ℓ:ℕ}(N: Captain H n' q t d Y A b t' f₀ k ℓ Chi.canonical)
namespace Burst10
open Daisy.Charity.RG12 Matter Height Shield Stained
-- Drop packets by markSeed(derived on algebra not parity). Drop K explicitly because roster incidence. No generic subtraction. Then in warm molecules only Miniature and Signed Cubic. Horn criterion employed.
section masks
private lemma moo (U:Config G c)(p:H.ThinP)(h:¬ Matter.troupe T R Q.halo (radiusB x) p.val) : leaflet H Chi.canonical U p=0:=by
  unfold leaflet likely; rw [Finset.sum_eq_zero,mul_zero]; intro i hi
  unfold Stained.fringe Shield.shelter; refine integral_eq_zero_of_ae ?_; filter_upwards with z; split; next hi=> exact False.elim (h hi.2)
  rfl
private lemma collectCells {w:Leaf R} (i:H.fragrances) {V0:Config G c}(h:matin w H i Chi.canonical V0 ≠ 0): ∃ j : Option (Fin i.1), w.turn.badge S ∈ (i.2 j).val ∧ ∀ k,Matter.troupe T R Q.halo (radiusB x) (i.2 k).val:=by
  unfold matin at h
  by_contra hh; push Not at hh
  apply h; rw [Finset.sum_eq_zero,mul_zero]; intro j hj; by_cases he : w.turn.badge S∈ (i.2 j).val
  · obtain ⟨k,hk⟩:=hh j he; by_cases hz:k=j
    · subst k; rw [libs,theme w _ _ hk]; simp
    rw [prod_eq_zero (mem_erase.mpr ⟨hz,mem_univ _⟩) (moo H _ _ hk),zero_mul]
  rw [libs,sunset w _ _ he]; simp
set_option quotPrecheck false
local notation "amt" => Height.overlap H
local notation "aw" => Daisy.Charity.RG12.cold H r.live.turn
open Pressure.Stores
private lemma neat (i:H.fragrances) (ht: Height.overlap H i=0){j:Option (Fin i.1)}(hv:Matter.troupe T R Q.halo (radiusB x) (i.2 j).val)(k:Stores S): Sum.inl k ∉ (i.2 j).val:=by
   intro hk; have hh:k.shares ≤ Height.overlap H i:= by
      have ht:k.shares ≤ Cash.numP (i.2 j).val:= Finset.single_le_sum (s:=(i.2 j).val) (f:=fun x => Push.AbsoluteSums.Mixed.shares S x) (fun i _=> Nat.zero_le _) hk
      exact ht.trans (Finset.single_le_sum (f:=fun j=> Cash.numP (i.2 j).val) (fun i _=>Nat.zero_le _) (mem_univ j))
   have he:1≤ k.shares:=Packets.shares_nonzero S _ _ (hv.1.checkpoints k (mem_toLeft.mpr hk))
   omega
private lemma needE (i:H.fragrances) (ht:amt i=0){j:Option (Fin i.1)}(hv:Matter.troupe T R Q.halo (radiusB x) (i.2 j).val)(k:ℕ): Sum.inr (Sum.inl k) ∉ (i.2 j).val:=by
   intro hk; set Y:=(i.2 j).val
   have hh: Y.toLeft=∅:= Finset.eq_empty_iff_forall_notMem.mpr (fun q hq=> neat H _ ht hv q (mem_toLeft.mp hq))
   have hz:k∈ Matter.own Y:=mem_toLeft.mpr (mem_toRight.mpr hk)
   obtain ⟨p,hp⟩:= (R.activities.forced k).inventory_ne
   obtain ⟨Z,hZ,hB⟩:= hv.2.2 k hz p hp
   have h:Z∈ (Matter.roster Y).costs:=hZ
   unfold Matter.roster at h; rw [hh] at h; simp [Packets.store] at h
local notation "Canonical"=> Chi.canonical
private lemma warm_speakers {i:H.fragrances}(hp: pane H r v i ≠0): ∃ j : Option (Fin i.1), r.live.turn.badge S∈ (i.2 j).val∧∀ k,Matter.troupe T R Q.halo (radiusB x) (i.2 k).val :=by
  by_contra h
  have hh {w:Leaf R} (he:w.turn=r.live.turn) :matin w H i Canonical = 0:=by
     funext V; refine not_not.mp ?_
     intro hk; exact h (he ▸ collectCells H i hk)
  apply hp; have hz{c}: (Complex.ofReal ∘ (0:Config G c→ℝ))=0:=by ext; simp
  rw [pane,hh rfl,hh r.together.symm,hz,smul_zero,add_zero,smul_zero]
-- hp warm contributes if orientation geometry eligible.Since actual pane contains both, either support forces.
open Labels Source
-- exact spelling of remaining prior. cubic & small ONLY
abbrev cubeHead (p: Raw.Trans f): Head S:=.inr (.inr (.inl (.inl (.inr (.inl p)))))
abbrev miniHead (p: Coat.Miniature c f): Head S:= .inr (.inr (.inl (.inr (.inl p))))
def bulb (p:Head S):Prop:= (∃ i:Raw.Trans f, p=cubeHead i) ∨ ∃ i: Coat.Miniature c f,p=miniHead i
lemma beam_chip {p:Head S}(hs:sign11 p<1)(hL:∀ i:Stores S,p≠ .inl i)(hv:∀ k:ℕ,p≠ .inr (.inl k)) : bulb p :=by
   rcases p with p|p|p|p; · exact (hL p rfl).elim
   · exact (hv p rfl).elim
   · rcases p with p|p|p; swap; · exact Or.inr ⟨p,rfl⟩
     rcases p with p|p|p|p|p|p -- zero horn only second
     · exact False.elim (Nat.lt_irrefl 1 hs)
     · exact Or.inl ⟨p,rfl⟩
     · exact False.elim (Nat.lt_irrefl 1 hs)
     · exact False.elim (Nat.lt_irrefl 1 hs)
     · change 2<1 at hs; omega
     · change 2<1 at hs; omega
     change 2<1 at hs; omega
   change 2<1 at hs; omega
set_option quotPrecheck false
local notation "Tag" => r.live.turn.badge S
/-- Comes with deterministic lowering for M with gas turn: !prince in that case, ALL entries suppressed by Parem.
 Explicit same for log marks on any regular lineage.S. retainer compare. -/
structure Warmed (r: Cloud R)(i:H.fragrances):Prop where -- fallback
   fields : i.1+1 ≤ hue H i ∧ hue H i≤2
   choice : ∃ (j:Option (Fin i.1)), r.live.turn.badge S ∈ (i.2 j).val ∧ ∀ (u : Option (Fin i.1)) (a:Head S), a∈(i.2 u).val → (j=u∧a=r.live.turn.badge S) ∨ bulb a
   notPetrol : ∃ j:ℕ,r.live.turn=.logKey j
lemma guides11 (g:Source.Hol G){p:H.fragrances}(h:warm11 (B:=B) H r o v F g p≠0): Warmed H r p :=by
   have hh : ¬ Daisy.Charity.RG12.cold H r.live.turn p:= fun hp=>h (if_pos hp)
   have hz : Height.overlap H p=0:=not_not.mp (fun ht=>hh (Or.inl (Or.inr ht)))
   have he : pane H r v p ≠0:= by
      rw [warm11, if_neg hh] at h; intro hr; unfold rows10 at h; rw [hr] at h; simp [Push.Local.weighted] at h
   obtain ⟨k,hk,hp⟩:= warm_speakers H r v he
   have hS(i:H.ThinP):1≤ i.val.card:= Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr (by
      obtain ⟨u,ht⟩:= i.2.1; intro hh; change u∈ i.val.biUnion H.supportP at ht; rw [hh] at ht; simp at ht))
   have hLo : p.1+1 ≤ hue H p:=(show p.1+1 = ∑ _i:Option (Fin p.1),1 by simp).trans_le (sum_le_sum (fun i _=>hS (p.2 i)))
   refine ⟨⟨hLo,Nat.le_of_lt_succ (lt_of_not_ge (fun hp=> hh (Or.inl (Or.inl hp))))⟩, ⟨k,hk,fun j a ha=>?_⟩,?_⟩
   swap
   · rcases he:r.live.turn with q|q
     · exact ⟨q,rfl⟩
     exact (needE H p hz (hp k) q (show _∈_ from by rw [he] at hk; exact hk)).elim
   let X:=r.live.turn.badge S
   by_cases hr:k=j∧a=X
   · exact Or.inl hr
   right
   have ht i (c:Head S)(h:c∈(p.2 i).val): sign11 c ≤ pins S (p.2 i).val:= Finset.single_le_sum (f:=fun q=>sign11 q) (s:=(p.2 i).val) (fun i _=>Nat.zero_le _) h
   apply beam_chip (hL:=fun i hi=>neat H p hz (hp j) i (hi ▸ ha)) (hv:=fun i hi=>needE H p hz (hp j) i (hi ▸ ha))
   by_contra hf
   have hf:1 ≤ sign11 a:=le_of_not_gt hf
   by_cases hv:k=j
   · subst j; have hs:a≠X:=fun hp=>hr ⟨rfl,hp⟩
     have hpp:1≤(Finset.erase (p.2 k).val X).card:= card_pos.mpr ⟨_,mem_erase.mpr ⟨hs,ha⟩⟩
     rw [card_erase_of_mem hk, Nat.one_le_iff_ne_zero] at hpp
     have hv : 2 ≤ hue H p:= (by omega : 2≤ ((p.2 k).val:Finset _).card)|>.trans (Finset.single_le_sum (s:=univ) (f:=fun i=> (p.2 i).val.card) (fun i _=>Nat.zero_le _) (mem_univ k))
     have he : sign11 X + sign11 a≤ pins S (p.2 k).val:=by
        unfold pins; change _ ≤ ∑ i∈_, sign11 i; rw [← Finset.add_sum_erase _ sign11 hk]; exact add_le_add_right (Finset.single_le_sum (f:=fun i=>sign11 i) (fun _ _=> by simp) (mem_erase.mpr ⟨hs,ha⟩)) _
     exact hh (Or.inr ⟨(Nat.add_le_add_left hf _).trans (he.trans (Finset.single_le_sum (f:=fun i=>pins S (p.2 i).val) (fun _ _=>by simp) (mem_univ k))),hv⟩)
   have hm(i j:Option (Fin p.1))(hq:j≠i)(f:Option (Fin p.1)→ℕ): f i+ f j ≤ ∑ q,f q:= by
      rw [← add_sum_erase _ f (mem_univ i)]; exact add_le_add_right (Finset.single_le_sum (f:=f) (fun _ _=>by simp) (mem_erase.mpr ⟨hq,mem_univ _⟩)) _
   exact hh (Or.inr ⟨(add_le_add (ht k X hk) (hf.trans (ht j a ha))).trans (hm k j (Ne.symm hv) (fun i => pins S (p.2 i).val)), ((Nat.add_le_add (hS (p.2 k)) (hS (p.2 j))).trans (hm k j (Ne.symm hv) (fun i=> (p.2 i).val.card)))⟩)
end masks
end Burst10
end prices
end YM.PhysicalNext.Repeat.Blush
