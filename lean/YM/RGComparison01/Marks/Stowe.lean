import YM.RGComparison01.Marks.Staircase
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Pledge
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter Mixed Reserves
open PhysicalNext PhysicalNext.Repeat Packets Art Silica Poll Pond Shield Eider Gas Ursell Trees Height Sail
open PhysicalNext.Repeat.Lotus Team Merge
open AnalyticBridge VerifiedReset Collection Quotes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge} {ι : Type} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {R : RG.Rep G f}
    {n : ℕ} {W a r σ Λ μ s κ w c' C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
    {d C' A B e δ t D D' v K :ℝ} {j k ℓ:ℕ} {χ:Chi}
    {Ψ : ℕ → Prop} {x:ℕ→ℝ}
/-!
# Lifting the core: bounded-label portion

 Literal basis Σ preserving exact roots, valuations and readability. Here
 can use an arbitrary Catalog (`Cabinet`). Part retained *after* bearing on
 all integer multiplicities (bounded use), all unpriced paid outside. All
 mark sets, not changing works. -/
namespace Stowe
open Foreman Checks Baked Palette Pillow Resin Season Ink Heron
open Switch Mallow Ovens OmitClusters Song Refrain Motion
variable {η β: Type} [Fintype ι]
variable (M:ι→Lotus.Leaf R)(g:ι→ℝ)(H:Cash W s μ L Q o C T R)
    {b t :ℕ} (Z:Cabinet η H b)
local notation "Xp"=> Tickets (Palette.sign M S)
-- support at p; aperture requires even disjoint (CLEAN works for arcs)
def recordSet (z:Cl M H) : Finset ι := univ.biUnion fun i=> (z.2 i).2.val
def Yielding (p:Finset ι) (z:Cl M H):= recordSet M H z=p ∧ Season.allot z=p.card
def struck (p:Finset ι) (z: Cl M H) := Yielding M H p z ∧ (∀ i,(z.2 i).2.reach⊆(z.2 i).1.val)
-- ledger
set_option quotPrecheck false
local notation "ZA"=>Cabinet.Record Z ℓ
local notation "YC"=>Pillow.Tags M (S:=S)
abbrev coatP (z:Cabinet.Record Z ℓ) := Ink.spore M H (Z.covers z)
abbrev ride (t: ZA) (i:coatP M H Z t) := Ink.pollen M H (Cabinet.covers Z t) i

def loom (ℓ:ℕ) : (Σ t:Cabinet.Record Z ℓ, coatP M H Z t) ↪ Cl M H := ⟨fun i=> ride M H Z i.1 i.2,by
  rintro ⟨i,j⟩ ⟨p,x⟩ hh
  have he:Ink.span M H _= _ := congr_arg (Ink.span M H) hh
  obtain rfl: i=p:= (Z.bureau ℓ).injective (congr_arg Sigma.fst he);
  have he:j=x:= Sigma.mk.inj_iff.mp he|>.2 |> eq_of_heq -- maybe edit
  subst x; rfl⟩
def header (ℓ k:ℕ) := ((Z.podium ℓ k).sigma fun _=> Finset.univ).map (loom M H Z ℓ)
def ledger (ℓ k:ℕ) (p:Finset ι) : Finset (Cl M H):= (header M H Z ℓ k).filter (struck M H p)
lemma posted (p:Cl M H)(ℓ k:ℕ): p∈header M H Z ℓ k ↔ ∃ v ∈ Z.podium ℓ k,Z.covers v=Canyon.pattern p:= by
   constructor
   · intro h; obtain ⟨⟨t,i⟩,hp,rfl⟩:= mem_map.mp h; exact ⟨t,(mem_sigma.mp hp).1,rfl⟩
   rintro ⟨t,ht,hp⟩; have hh: Z.covers t=(Ink.span M H p).1:=hp; let v:=Ink.span M H p; let i:spore M H (Z.covers t):= cast (congr_arg (spore M H) hh.symm) v.2
   refine Finset.mem_map.mpr ⟨⟨t,i⟩,Finset.mem_sigma.mpr ⟨ht,Finset.mem_univ _⟩,(Ink.span M H).injective ?_⟩
   change Sigma.mk (β:=spore M H) (Z.covers t) i=v; have hI : Z.covers t=v.1:=hh; exact Sigma.ext hI (cast_heq ..) -- may need explicit
omit [Fintype ι] in
lemma concur (z:Cabinet.Record Z ℓ) (i: coatP M H Z z): Cabinet.ground Z z.val= Baked.origins M H (ride M H Z z i) := rfl

-- ROOT footprints: # any choice. small-orbit prefix. not necessarily log needed.
def Engaged (V: ι→Site f) := ∀ i,V i∈(M i).crest
omit [Fintype ι] in
lemma enrolled (i:ι): (M i).crest.image S.ratio.parent ⊆ H.supportP (Palette.sign M S i) := by
   change _ ⊆ areas R T Q.halo (radiusB s) _; rw [Palette.sign,Wing.badge_area]; exact Finset.Subset.trans (Finset.image_subset_image (show (M i).crest⊆RG.inspected ((M i).turn.support R) from subset_union_left)) (halo_subset _ _)
-- geometry: slots retained exactly get anchor-bound
omit [Fintype ι] in
lemma crest (p:Finset ι)(z:Cl M H)(hp:struck M H p z)(i:ι)(hi:i∈p) : (M i).crest.image S.ratio.parent ⊆ origins M H z := by
   have ht : i∈ recordSet M H z:=hp.1.1.symm ▸ hi
   obtain ⟨k,hk,hv⟩:= mem_biUnion.mp ht
   have he: Palette.sign M S i ∈ (z.2 k).1.val := hp.2 k ((z.2 k).2.reaches_of hv)
   exact Finset.Subset.trans (enrolled M H i) (Finset.Subset.trans (subset_biUnion_of_mem H.supportP he) (subset_biUnion_of_mem (raised M H ∘ z.2) hk))
-- authorize diameter for each pose (needed to reanchor HELD costs)
lemma traits (p:Finset ι) (x:Site c)(i:ι)(hi:i∈p)(he: x∈(M i).crest.image S.ratio.parent) (z:Cl M H)(hz:z∈ledger M H Z ℓ k p): x∈ origins M H z ∧ origins M H z ⊆ neighbors (Cabinet.garage b ℓ) x := by
  have h₀:= (mem_filter.mp hz).2; have hp:= crest M H p z h₀ i hi he; refine ⟨hp,?_⟩; obtain ⟨v,hv,rfl⟩:= mem_map.mp (mem_filter.mp hz).1; rw [← show Cabinet.ground Z v.fst.val= origins M H (loom M H Z ℓ v) from rfl] at hp ⊢; exact Z.extent _ x hp
lemma strides (p:Finset ι) (z:Cl M H)(hp:z∈ ledger M H Z ℓ k p) (i:ι)(hi:i ∈ p)(V: ι→Site f)(he:Engaged M V) :
   ∀ j∈p, S.ratio.parent (V j)∈ neighbors (Cabinet.garage b ℓ) (S.ratio.parent (V i)):= fun j hj=> (traits M H Z p _ i hi (mem_image_of_mem _ (he i)) z hp).2
    (crest M H p z (mem_filter.mp hp).2 j hj (mem_image_of_mem _ (he j)))
-- content and Transport on all Healthy at family

abbrev tale (ℓ k:ℕ) (p:Finset ι) := ∑ z∈ ledger M H Z ℓ k p,glass M g χ z
def ship (ℓ k:ℕ) (p:Finset ι) (V:Config G c):= ∑ z∈ledger M H Z ℓ k p,pottery M g χ z V -- fix
lemma stay (P:BudgetPoint)(h:∀ z:Cl M H, P.Regular (origins M H z) (glass M g χ z))
  (p:Finset ι) (x:Site c)(i:ι)(hi:i∈p)(hp:x∈(M i).crest.image S.ratio.parent): P.Regular (neighbors (Cabinet.garage b ℓ) x) (tale M g H Z ℓ k p (χ:=χ)):= Meadow.regularA _ fun z hz=> CouplingShape.reg_extend (h z) (traits M H Z _ _ _ hi hp _ hz).2

lemma standing (t:ℝ) (h:∀ z:Cl M H,pottery M g χ z= masked t (origins M H z) (glass M g χ z))
  (p:Finset ι) (x:Site c) (i:ι)(hi:i∈p)(hp:x∈ (M i).crest.image S.ratio.parent) (V:Config G c)(hv:Healthy t (neighbors (Cabinet.garage b ℓ) x) V): ship M g H Z ℓ k p V (χ:=χ) = tale M g H Z ℓ k p V (χ:=χ):= by
   rw [tale,Finset.sum_apply]; exact Finset.sum_congr rfl fun z hz=> (congr_fun (h z) V).trans (masked_eq t _ _ _ (hv.mono_left (traits M H Z _ _ _ hi hp _ hz).2))
end Stowe
end YM.RGComparison01.Pledge
