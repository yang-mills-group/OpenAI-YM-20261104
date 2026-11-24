import YM.Juniper.Flare.Cohort
import YM.Juniper.Bright.Promise
/-!
 # Input E-letter tapes, lift receipts on the physical orbit

 Don't fundamentally require a *finite* reg model, or clean zero-activity
 padding at all locations in a template (would be delicate after
 seat canonicalization). Use finite exhaustion like Bright.Peering. Ask for
 cover-lift properties only for the selected finite list, each visit, with
 selected footprints. Unbounded in size as visits increase. The *locality*
 restriction is that ALL nonzero E letters of the chosen model fit in that
 upgrade (where `m` not RG scale but index of truncation/exhaustion);
 long Laurent path tails can be erased first, paid in the cumulative E
 account, never claim pure pressure erases them automatically.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.Juniper.Flare
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter
open PhysicalNext PhysicalNext.Repeat Deck Mint Stellar Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C F : Side} {P : Patch} {M D' : ℕ} {K : Teller G}

section localH
variable {S : StepData c f} {T : Tube G S} {R : Rep G f} {p : ℝ}
variable {m l B j : ℕ}
structure Tape (g : Ratio c f) (R : Rep G f) (B l : ℕ) where
  names : ℕ → Finset ℕ
  -- use bound permitting radius *coarse*. Smaller halls, already bought.
  halls (m i) : i∈ names m → Raw.regularFoot g l B R i ⊆ neighbors (Mint.width l B B) (g.parent (fanchor R i))
  covers : ∀ i, (∃ V, R.activities.regularOccurrence R.p i V≠0) → ∀ᶠ m in atTop, i ∈ names m

-- low selection depends on hatted p and faithful queries only
variable (U : Tape S.ratio R (radiusB p) l)
local notation "B" => radiusB p
-- allow omit copying orientation for regular-only.
def lampset (m:ℕ): Finset (TypeLetter c f) := Finset.disjSum (Bright.firstPrice (R:=R) (x:=p) m) (U.names m)
lemma shape (h : 0<radiusB p) {i:TypeLetter c f} (hi:i∈ lampset U m):
    post S R i∈areas R T l (radiusB p) (sites S i) ∧ areas R T l (radiusB p) (sites S i)⊆ neighbors (Mint.width l B B) (post S R i):= by
  cases i with
  | inl i => exact Mint.centered l (B) (B) h i S T R ((mem_filter.mp (inl_mem_disjSum.mp hi)).2)
  | inr i =>
    exact ⟨halo_subset _ _ (mem_image_of_mem _ (show fanchor R i∈inspected (R.activities.reg i).support from mem_union_left _ (R.activities.reg i).anchor)),U.halls _ _ (inr_mem_disjSum.mp hi)⟩

variable {a b u w : ℝ} {J : ConnectedActivityE6.Target G K}
    {o : ConnectedActivityE6.Target.Order G w} {L : Side}
    (I : Cash w p u L J o a T R) {χ:Chi}
open Bright
-- keep all existing site charging logic, actually meets Thick γ horizon
variable (Y : Tape S.ratio R (radiusB p) J.halo)
def portal (m:ℕ) : Bright.Shelf I (Mint.width J.halo (radiusB p) (radiusB p)):= by
   let P:= sites S; let Z:= (lampset Y m); let f : Head S→ Site c:= extend P (post S R) 0
   refine ⟨Z.map P, ?_, f,?_,?_⟩
   · intro s hs; let x:= Z.filter fun i=> P i∈s; have hX:x.map P=s:= by
        ext i; constructor
        · intro hi; obtain ⟨j,hj,rfl⟩:= mem_map.mp hi; exact (mem_filter.mp hj).2
        intro hi; obtain ⟨j,hj,rfl⟩:= mem_map.mp (hs hi); exact mem_map_of_mem _ (mem_filter.mpr ⟨hj,hi⟩)
     exact hX ▸ (congr_arg (·.flags) (no_roster S x) : (roster (x.map P)).flags=_)
   all_goals
     intro i hi; obtain ⟨j,hj,rfl⟩:=mem_map.mp hi; rw [show f (P j) = post S R j from P.injective.extend_apply ..]; have h:= I.laws.data.room.sight.1
     first| exact (Flare.shape (T:=T) Y (by omega) (m:=m) hj).1| exact (Flare.shape (T:=T) Y (by omega) (m:=m) hj).2

lemma lightWindow (i : TypeLetter c f) (x : Site c) (n k:ℕ) :
    (sites S) i ∈ (portal I Y n).Window k x ↔ i∈ lampset Y n∧ separation x (post S R i) ≤ Shelf.terrace (Mint.width J.halo (radiusB p) (radiusB p)) k := by
  rw [Shelf.Window,mem_filter]; change _ ∈ ((lampset _ _).map (sites S)) ∧ extend (sites S) _ _ ((sites S) i) ∈ _ ↔ _; rw [Finset.mem_map',(sites S).injective.extend_apply,neighbors_mem]

open Blaze Silica March Captain Refrain Song
lemma covers_high (k:ℕ) (z:I.fragrances) (hp : Song.opus I (Bright.blank I) χ b (.inl z)≠0) (hk:¬Bright.high I k z) : ∀ᶠ n in atTop, z∈ (portal I Y n).slate k := by
   obtain ⟨V,hV⟩:= Function.ne_iff.mp hp
   have he:stream I χ V z≠ 0 := by simpa [opus,Song.sequence,Bright.every] using hV
   have h i : ∀ᶠ n in atTop, (z.2 i).val⊆(portal I Y n).binders:= by
     apply (eventually_all_finset _).2; intro j hj
     rcases Bright.material_head I z he hk i hj with ⟨i,rfl,h⟩ | ⟨i,rfl,h⟩
     · filter_upwards [Y.covers i h] with n hn using (mem_map_of_mem (sites S) (a:=Sum.inr i) (inr_mem_disjSum.mpr hn))
     filter_upwards [eventually_ge_atTop (Meadow.held i)] with n hn
     have hv : i∈Bright.firstPrice (x:=p) (R:=R) n:=mem_filter.mpr ⟨(Meadow.pocket ..).2 hn,h⟩
     exact mem_map_of_mem (sites S) (inl_mem_disjSum.mpr hv)
   filter_upwards [eventually_all.mpr h] with n hn using Shelf.in_slate _|>.mpr (Shelf.ensured _ z he hk hn)
end localH

section bridge
variable {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {Q : KernelChoices} {hC : C.val=c.val*M} {he:2 ≤ c.val}
local notation "L" => Lace.project (h:=h) (H:=H) hC he
local notation "S" => stepped Q h
local notation "Y" => stepped Q H
variable {T : Tube G (stepped Q h)} {T' : Tube G (stepped Q H)} {p : ℝ}
    {R:RG.Rep G f} {R':RG.Rep G F}
variable {a b u w : ℝ} {J : ConnectedActivityE6.Target G K}
    {o : ConnectedActivityE6.Target.Order G w} {L₀ : Side}
    (I : Cash w p u L₀ J o a T R) (I' : Cash w p u L₀ J o b T' R')
open Bright
local notation "B" => radiusB p
local notation "μ" => Mint.width J.halo (radiusB p) (radiusB p)
variable {B' l m : ℕ} {U : Tape (decreed h) R (radiusB p) J.halo}
   {U' : Tape (decreed H) R' (radiusB p) J.halo}
/-- Projection over chosen E template. Enumeration coherence needed only on
 the used finite exhaustion. -/
structure Volume (e : Lace h H M) (U' : Tape (decreed H) R' B' l)
    (U : Tape (decreed h) R B' l) (m:ℕ) where
   π : ℕ → ℕ
   reads i : i∈U'.names m → π i∈ U.names m ∧ Pair e R' R i (π i)
   serves j (x : Site C) : j∈U.names m → (decreed h).parent (fanchor R j)= e.low.cut x →
       ∃ i, i∈U'.names m∧π i=j∧ (decreed H).parent (fanchor R' i)=x
   uniqueness i j : i∈U'.names m → j∈U'.names m → π i=π j →
       (decreed H).parent (fanchor R' i)=(decreed H).parent (fanchor R' j) → i=j

variable (V : Volume (Lace.project (h:=h) (H:=H) hC he) U' U m) (hp : R'.path=R.path)
local notation "π" => V.π
local notation "ω" => Flare.track (L) (V.π)
local notation "u₀" => post (S) R
local notation "u₁" => post (Y) R'
local notation "F₀" => lampset («S»:=S) U m -- syntax
local notation "F₁" => lampset («S»:=Y) U' m
include hp he I I'
lemma Volume.moved (i:TypeLetter C F) (hi:i∈ F₁): ω i ∈ F₀ ∧ Pertinent (L) (V.π) B R' R i:= by
   cases i with
   | inl i => have hv:=inl_mem_disjSum.mp hi; exact ⟨inl_mem_disjSum.mpr ((Bright.chosen hC he I' I hp m i).1 hv), (mem_filter.mp hv).2⟩
   | inr i => exact ⟨inr_mem_disjSum.mpr ((V.reads i (inr_mem_disjSum.mp hi)).1),(V.reads i (inr_mem_disjSum.mp hi)).2⟩
omit hp I I'
lemma Volume.major (i:TypeLetter C F)(hi:i∈ F₁) : Macrame.splitter (Deck.divides hC) (u₁ i)= u₀ (ω i):= by
   cases i with
   | inl i => exact (Stellar.nest_mint (h:=h) (H:=H) (Q:=Q)).footing i -- implicit
   | inr i =>
      let e := Lace.project (h:=h) (H:=H) hC he
      exact ((L).position (fanchor R' i)).symm.trans (congr_arg e.r.parent (V.reads i (inr_mem_disjSum.mp hi)|>.2.sends))
include hp I I'
-- existing Nest requires map of EVERY LETTER on ℕ, too strong. produce a restricted Nest.
def Volume.depart : ↥(lampset («S»:=Y) U' m) → ↥(lampset («S»:=S) U m) := fun i=> ⟨ω i.val,(Volume.moved I I' V hp i.val i.2).1⟩
lemma Volume.trail : Nest (Deck.divides hC) (Volume.depart I I' V hp) (u₁ ∘ Subtype.val) (u₀ ∘ Subtype.val):= by
   refine ⟨fun i=> V.major _ i.2, fun i j hj=> ?_,fun i j hh heq=> Subtype.ext ?_⟩
   · rcases j with ⟨j|j,hj'⟩
     · let N:= @Stellar.nest_mint c f C F P M h H Q hC he -- arg order check
       obtain ⟨k,hk,hK⟩:= N.extend i j hj; have hz : k∈ Bright.firstPrice (x:=p) (R:=R') m:= (Bright.chosen hC he I' I hp m k).2 (hk.symm ▸ inl_mem_disjSum.mp hj')
       exact ⟨⟨_,inl_mem_disjSum.mpr hz⟩,Subtype.ext (congr_arg Sum.inl hk),hK⟩
     obtain ⟨k,hk,hK,hX⟩:=V.serves j i (inr_mem_disjSum.mp hj') hj
     exact ⟨⟨_,inr_mem_disjSum.mpr hk⟩,Subtype.ext (congr_arg Sum.inr hK),hX⟩
   have hx:=congr_arg Subtype.val hh; rcases i with ⟨i|i,hi⟩; all_goals rcases j with ⟨j|j,hj⟩
   · exact congr_arg Sum.inl ((Stellar.nest_mint (h:=h) (H:=H) (Q:=Q) (hC:=hC) (he:=he)).firm i j (Sum.inl_injective hx) heq)
   · contradiction
   · contradiction
   exact congr_arg Sum.inr (V.uniqueness i j (inr_mem_disjSum.mp hi) (inr_mem_disjSum.mp hj) (Sum.inr_injective hx) heq)
end bridge
end YM.Juniper.Flare
