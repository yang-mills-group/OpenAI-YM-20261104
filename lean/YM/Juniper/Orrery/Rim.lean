import YM.Juniper.Orrery.Pencil
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Orrery
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 PhysicalNext PhysicalNext.Repeat Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Further.PhysicalPeriodLimitF933 Macrame Deck Flare
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof Roost Input Supply Slide
open Progress.DirectedRecipe UVExtension Height StressFlux
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
/-!
 # Covers and short E (the after-epoch terms)

 A path may be VERY LONG. But paths never skip a lattice site. Prove exact iff
 fit if both periods sufficiently large. (Small price alone of twirl tail
 would not be input theorem at arbitrarily large n.)
 -/
variable {G:Gauge} {c C:Side} {k:ℕ} {ρ:ℝ}
section lifting
variable (hC:C.val=c.val*k) (x:Site C) (P: BudgetPoint)
local notation "F"=> (Macrame.normal (Deck.divides hC) hC)
local notation "H"=> (Macrame.splitter (Deck.divides hC))
local notation "B"=> P.B
local notation "W"=> wrap C
variable (V:Curtain G c) (T:Curtain G C) (hm:Margin P c)
variable {X Y:Type*} (U: Config G c)
local notation "E"=> ((F).links U)
open Meadow
variable (S : PathData G) (t:Clip) (α β:ℝ)
section reach
include hC hm
private lemma arc (a:Cover) (w:Walk) (x:Cover) (ha : separation (0:Site C) (W a) ≤ B)(hr : ∀ b∈visits a w,separation (0:Site c) (H (W b))≤B)(hx:x∈visits a w): separation (0:Site C) (W x) ≤ B:=by
    induction w generalizing a with
    | nil=> rw [show x=a from List.mem_singleton.mp hx]; exact ha
    | cons i w ih=>
       rcases List.mem_cons.mp hx with hi|hi; · subst x; exact ha
       let b:= a+i.vec; have hz (x) (hx:x∈visits b w):= hr x (List.mem_cons_of_mem _ hx)
       apply ih b ?_ hz hi; have h : separation (W a) (W b) ≤ 1:= by unfold b; rw [map_add,wrap_vec]; exact UVNext.PricedKernels.oneStep_le ..
       rw [Deck.teaches (Deck.divides hC) 0 (W b) (by have hx:=separation_triangle (0:Site C) (W a) (W b); unfold Margin at hm; omega),map_zero]
       exact hz b (by cases w <;> simp [visits])
private lemma rim_track (Q: Slot)(h:∀ x∈Wages.walkCuts Q (0:Site C), separation (0:Site c) (H x) ≤ B) : Wages.walkCuts Q (0:Site C) ⊆ neighbors B 0:= by
    intro x hx; obtain ⟨p,hp,rfl⟩:= mem_image.mp hx; rw [add_zero,neighbors_mem]; have hh y (hy:y∈Q.stencil) : separation (0:Site c) (H (W y)) ≤ B:=h _ (Finset.mem_image.mpr ⟨y,hy, add_zero _⟩)
    have hx x (hx:x∈ visits 0 Q.walk): separation (0:Site C) (W x) ≤ B:= arc hC P hm 0 Q.walk _ (by simp) (fun p hp=>hh p (mem_union_left _ (List.mem_toFinset.mpr hp))) hx
    obtain ha|he:= Finset.mem_union.mp hp; · exact hx _ (List.mem_toFinset.mp ha)
    have ha (l:Walk) (x:Cover) : stop x l ∈ visits x l:= by induction l generalizing x <;> simp_all [visits, stop]
    exact arc hC P hm Q.offset _ p (hx _ (ha Q.walk 0)) (fun x h=> hh x (mem_union_right _ (List.mem_toFinset.mpr h))) (List.mem_toFinset.mp he)
omit hm
lemma walkdown (i:Slot) : Wages.walkCuts i (H x)=(Wages.walkCuts i x).image H:= by unfold Wages.walkCuts; rw [image_image]; exact Finset.image_congr fun i hi=> ((F).rooted ..).symm
lemma low_home (j: Low)(x:Site C): Low.home S j P (H x)=(Low.home S j P x).image H:= by
   unfold Low.home; have hh : halo B ({H x}: Support c)=(halo B {x}).image H:=by rw [← Finset.image_singleton]; exact Deck.ringed hC _ _
   cases e:j.2 <;> simp only [Sum.elim_inl,Sum.elim_inr,hh,image_union,walkdown hC]
include hm
lemma low_rim (j:Low)(h : ∀ x∈ Low.home S j P (0:Site C), separation (0:Site c) (H x) ≤ B): Low.home S j P (0: Site C) ⊆ neighbors B 0:= by
   intro x hx; have hp{y:Site C}(hp:y∈halo B {0}): y∈neighbors B 0 := (neighbors_mem ..).mpr (by simpa only [halo_spec,mem_singleton,exists_eq_left] using hp)
   unfold Low.home at hx; cases hj:j.2 with
   | inl k=> rw [hj] at hx; exact hp hx
   | inr i=>
      rw [hj] at hx; rcases mem_union.mp hx with hx|hx; · rcases mem_union.mp hx with hx|hx; exact hp hx; exact rim_track hC P hm (j.left S i) (fun x hx=>h x ((Low.walk_home S j P (0:Site C) hj).1 hx)) hx -- syntax wrong
      exact rim_track hC P hm (j.right S i) (fun x hx=>h x ((Low.walk_home S j P (0:Site C) hj).2 hx)) hx
lemma walks (j:High)(h:∀ x∈ High.home S j (0:Site C), separation (0:Site c) (H x) ≤ B): High.home S j (0:Site C) ⊆ neighbors B 0:= by
   let i:= j.term S; have hq (k:Fin j.arity){U:Site C}(hk: U∈ Wages.walkCuts (i.leg k) 0): U ∈ High.home S j (0:Site C) := by
      obtain ⟨v,hv,rfl⟩:= mem_image.mp hk; exact mem_image_of_mem _ (show v∈ i.stencil from mem_insert_of_mem (mem_biUnion.mpr ⟨k,mem_univ _,hv⟩))
   intro p hp; obtain ⟨v,hv,rfl⟩:= mem_image.mp hp; rcases mem_insert.mp hv with hv|hv; · subst v; rw [neighbors_mem]; simp
   obtain ⟨x,hx,hv⟩:= mem_biUnion.mp hv; exact rim_track hC P hm _ (fun u hu=> h u (hq x hu)) (mem_image_of_mem _ hv)
omit hm
end reach
section gems
include hC
local notation "Δ"=> (Averaging.delta (V.book.read V.stamp))
local notation "Z"=> (fun i:Seat C=>Meadow.pinch hC i)
lemma spreaded (i:Seat C)(f:Support C): (Z i).spread (f.image H)=(i.spread f).image H:=by unfold Seat.spread; rw [image_image,image_image]; exact Finset.image_congr fun v hv=>(Meadow.charts hC i v|>.symm)
lemma service (i:Slot) : i.atSite E x=i.atSite U (H x):= by unfold Slot.atSite; rw [(F).expansion]; rfl
lemma clove : petals (E) x=petals U (H x):=by have ht (a b:Step):plate (E) x a b=plate U (H x) a b:=congr_arg G.curvature ((F).traveller U x (Lattice.oriented a b)); funext i; simp only [petals,clover,StressFlux.stencil,ht]
lemma highac (j:High) : j.plain S x E=j.plain S (H x) U:= by unfold High.plain Atom.unmasked Slot.atSite; simp_rw [(F).expansion]; rfl
lemma lowac (j:Low): j.plain S x E=j.plain S (H x) U:= by
    unfold Low.plain; cases e:j.2; · exact congr_arg G.price ((F).traveller U x _)
    exact congr_arg₂ (fun a b:G.Color=>inner ℝ a b/2) (service hC x U _) (service hC x U _)
variable {p : ℕ→ℕ} (L:Leaves hC p T.book.reg T.stamp.logRead V.book.reg V.stamp.logRead T.sequence V.sequence)
    (he:Curtain.TidyC T P P.B ρ)(hp:Curtain.TidyC V P P.B ρ)(hG:G.Simple)
include L he hp hm hG U
lemma register (i:ℕ)(hi:i∈T.sequence): Residual.rebate (T.book.reg i) (T.stamp.logRead i) E=Residual.rebate (V.book.reg (p i)) (V.stamp.logRead (p i)) U:=by
    unfold Residual.rebate Residual.payout VerifiedReset.counter; simp only [Pi.sub_apply]; rw [L.truer i hi, show T.stamp.logRead i 1=V.stamp.logRead (p i) 1 from L.truer i hi 1,Orrery.ink_delta hC V T P L hp he hm hG i hi,clove hC,(L.root i hi).2]
omit L he hp hm hG
lemma low_capture (i: Low) : i.fresh S t x α E=i.fresh S t (H x) α U:= by unfold Low.fresh Low.proxy; rw [clove hC,lowac hC]
lemma high_capture (i:High): i.fresh S x α β E=i.fresh S (H x) α β U:= by unfold High.fresh; rw [highac hC]

end gems
end lifting
end YM.Juniper.Orrery
