import YM.LocalLTE.Tile.Clime
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Span
/-! Local LTE high-order representation/compatibility on supported tiles. Adapts
`PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Span`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Meadow
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C F L₀ : Side} {P : Patch} {J₀ M D' : ℕ} {K : Teller G}
variable {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {Q: KernelChoices} {hC:C.val=c.val*M} {he:2 ≤ c.val} {p a b W U V : ℝ}
local notation "L" => Lace.project (h:=h) (H:=H) hC he
local notation "S" => stepped Q h
local notation "Y" => stepped Q H
variable {T : Tube G (stepped Q h)} {T' : Tube G (stepped Q H)} {R:RG.Rep G f} {R':RG.Rep G F}
    {X : ConnectedActivityE6.Target G K} {o : ConnectedActivityE6.Target.Order G W}
    {I : Cash W p a L₀ X o U T R} {I' : Cash W p a L₀ X o V T' R'}
    (hC he)
local notation "B" => radiusB p
local notation "D" => roomSizeN J₀ X.halo B
local notation "t" => Mint.width X.halo B B
variable (x : Site C)
include hC he
omit hC he in
lemma engirdsN (v:Vines C F) (hv:StirN I' J₀ v) (hz:x∈Meadow.pasture I' v) (i): Meadow.ground I' (v.2 i)⊆neighbors D x:= (your (H:=I') (z:=v) i).trans (enteredN hv x hz)
lemma inquireN (v u: Vines C F) (hv:StirN I' J₀ v) (hu:StirN I' J₀ u) (hx:x∈Meadow.pasture I' v) (hk:x∈Meadow.pasture I' u) (hC':2 * D < c.val) (h:forward (L) u=forward (L) v): u=v:= by
  have he : u.fst=v.fst:= congr_arg (fun i : Vines c f=> i.fst) h; rcases v with ⟨n,v⟩; rcases u with ⟨m,u⟩; dsimp only at he; subst m
  unfold forward at h; injection h with h hh; congr 1; funext i; let V:=v
  apply genitive (Q:=Q) hC (by assumption) x hC' _ _ (congr_fun hh i)
  · intro j hk'; exact (neighbors_mem ..).1 ((your (H:=I') (z:=⟨_,u⟩) i|>.trans (enteredN hu x hk)) (centersN (hu.each i) hk'))
  intro j hk; exact (neighbors_mem ..).1 ((your (H:=I') (z:=⟨_,v⟩) i|>.trans (enteredN hv x hx)) (centersN (hv.each i) hk))
lemma ringsN (v:Vines C F) (hv:StirN I' J₀ v) (hx:x∈ Meadow.pasture I' v) (hp:2*D<c.val) (i) : Set.InjOn (verse_down (L)) (↑(v.2 i) : Set (Music C F)):= by
  have hI:= engirdsN x v hv hx i
  intro y hy z hz he; exact (nest_mint (Q:=Q) (hC:=hC) (he:=by assumption) (h:=h) (H:=H)).point hp x y z ((neighbors_mem ..).1 (hI (centersN (hv.each i) hy))) ((neighbors_mem ..).1 ((your (H:=I') (z:=v) i).trans (enteredN hv x hx) (centersN (hv.each i) hz))) he
variable (hp : R'.path=R.path)
include hp I I'
lemma receiptsN (z:Vines C F) (hZ:2*D'< c.val) (hz: Meadow.pasture I' z⊆ neighbors D' x) (hu: ∀ i,SeedN I' J₀ (z.2 i)) :
    coefficient (blocked (Meadow.ground I')) z.2=coefficient (blocked (Meadow.ground I)) (forward (L) z).2:= by
  apply movement; intro i j; let f:=Meadow.ground I'; have hf i: f (z.2 i)⊆neighbors D' x := (your (H:=I') (z:=z) _).trans hz
  have hm i s (hh:s∈z.2 i):separation x (pace Y s) ≤ D':= (neighbors_mem ..).1 (hf i (centersN (hu i) hh)); have hv i: ((Meadow.ground I ∘ (forward (L) z).2) i)=(f (z.2 i)).image (L).low.cut:= pitched hC he hp _
  have hy i : Meadow.ground I ((forward (L) z).2 i)= (f (z.2 i)).image (L).low.cut:= hv i
  apply or_congr; · exact ⟨fun hx=>congr_arg (wrappers (L)) hx,genitive hC he x hZ (hm i) (hm j)⟩
  unfold Ac.meets; rw [hy,hy]; constructor
  · rintro ⟨v,h,hx⟩; exact ⟨_,mem_image_of_mem _ h,mem_image_of_mem _ hx⟩
  rintro ⟨v,h',hx⟩; obtain ⟨z,hv,hj⟩:=mem_image.mp h'; obtain ⟨y,hy,hr⟩:=mem_image.mp hx
  -- compare labels via hZ; priority
  exact ⟨z,hv, ((garden hC x hZ) (hf _ hy) (hf _ hv) (hr.trans hj.symm)) ▸ hy⟩
lemma stitchesN (z:Vines C F) (hv:StirN I' J₀ z) (hk:x∈Meadow.pasture I' z) (hH:2 * D< c.val) : StirN I J₀ (forward (L) z) ∧ (L).low.cut x∈Meadow.pasture I (forward (L) z):= by
  have hS:= enteredN hv x hk
  refine ⟨⟨hv.small,fun i=> ?_,((receiptsN (I':=I') hC he x (I:=I) hp z hH hS hv.each) ▸ hv.moves)⟩,?_⟩
  · apply (seed_orderN (I:=I) (I':=I') hC he hp _ (ringsN hC he x z hv hk hH i) ((garden hC x hH).mono _)).1 (hv.each i)
    exact coe_subset.mpr ((your (z:=z) i).trans hS)
  rw [pitchRoll (I:=I) (I':=I') hC he hp z]; exact mem_image_of_mem _ hk
end YM.PhysicalNext.Repeat.Meadow
