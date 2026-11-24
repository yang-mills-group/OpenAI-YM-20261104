import YM.RGComparison01.Marks.Snowy
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
namespace Stowe
open Foreman Checks Baked Palette Pillow Resin Season Ink Heron
open Switch Mallow Ovens OmitClusters Song Refrain Motion
section iris
variable {η α: Type} (M:ι→Lotus.Leaf R)(g:ι→ℝ)(H:Cash W s μ L Q o C T R) {b t k :ℕ} (Z:Cabinet η H b)
variable (σ : α ↪ ι) (s': Finset α)
local notation "Md"=> M ∘ σ
local notation "YC"=> Pillow.Tags M (S:=S)
local notation "Yg"=> Pillow.Tags (Md) (S:=S)
def peeled (σ : α ↪ ι) : Pillow.Tags (M ∘ σ) (S:=S) ↪ Pillow.Tags M (S:=S):=
  ⟨fun j=> ⟨j.val.map σ,fun i hi k hk he=> by obtain ⟨i,hip,rfl⟩:=mem_map.mp hi; obtain ⟨k,hkp,rfl⟩:=mem_map.mp hk; exact congr_arg σ (j.prop hip hkp he)⟩,
    fun i j he=>Subtype.ext (Finset.map_injective _ (congr_arg Subtype.val he))⟩
lemma tips (t: Pillow.Tags Md (S:=S)): (peeled M σ t).reach=t.reach ∧ team M (peeled M σ t)= team Md t:= by
   constructor
   · change (t.val.map σ).image (Palette.sign M S)=t.val.image _; rw [Finset.map_eq_image,image_image]; rfl
   let f : YC:= peeled M σ t
   have hh: ∀ V U: PhysicalNext.Repeat.Lotus.Team R,V.own=U.own → V=U:=by rintro ⟨v,hv⟩ ⟨w,hu⟩ rfl; rfl
   apply hh; unfold team; dsimp only; change (t.val.map σ).image M= _; rw [Finset.map_eq_image,Finset.image_image]
-- supports
variable (p:Cl (M ∘ σ) H)
def growsP : Cl Md H ↪ Cl M H := ⟨fun z=> ⟨z.1,fun i=>((z.2 i).1,peeled M σ (z.2 i).2)⟩,by
   rintro ⟨i,j⟩ ⟨k,l⟩ he; obtain rfl : i=k:=congr_arg Sigma.fst he; injection he with he h; congr 1; funext i
   have ht:=congr_fun h i; exact Prod.ext (congr_arg (Prod.fst (β:=Pillow.Tags M (S:=S))) ht) ((peeled M σ).injective (congr_arg Prod.snd ht))⟩
local notation "p₁"=> growsP M H σ
lemma accord : recordSet M H ((p₁) p)=(recordSet Md H p).map σ := by
   ext t; constructor
   · intro h; obtain ⟨i,hi,hx⟩:= mem_biUnion.mp h; obtain ⟨j,hj,rfl⟩:=mem_map.mp hx; exact mem_map_of_mem σ (mem_biUnion.mpr ⟨i,hi,hj⟩)
   intro h; obtain ⟨i,hi,rfl⟩:=mem_map.mp h; obtain ⟨j,hj,hx⟩:= mem_biUnion.mp hi; exact mem_biUnion.mpr ⟨j,hj, mem_map_of_mem σ hx⟩
lemma acres (t : Cl M H) (hl: recordSet M H t ⊆ s'.map σ): t ∈ Set.range (p₁) := by
   have hv j (h:Pillow.Tags M (S:=S)) (he:(t.2 j).2=h): ∃ i:Pillow.Tags Md (S:=S),peeled M σ i=h:= by
     let p:= h.val.preimage σ σ.injective.injOn; have hp : p.map σ = h.val:= by
       ext k; constructor
       · intro h; obtain ⟨l,hl,rfl⟩:=mem_map.mp h; exact mem_preimage.mp hl
       intro h₀; obtain ⟨l,hℓ,rfl⟩:=mem_map.mp (hl (mem_biUnion.mpr ⟨j,mem_univ _,he.symm ▸ h₀⟩)); exact mem_map_of_mem σ (show l∈p from mem_preimage.mpr h₀)
     exact ⟨⟨p,fun i hi j hj he=>σ.injective (h.prop (mem_preimage.mp hi) (mem_preimage.mp hj) he)⟩,Subtype.ext hp⟩
   choose v h using fun j=> hv j _ rfl
   refine ⟨⟨t.1, fun i=> ((t.2 i).1,v i)⟩,congr_arg (Sigma.mk t.fst) ?_⟩
   exact funext fun i=> Prod.ext rfl (h _)
lemma readable : Season.allot (p₁ p)=Season.allot p:= Finset.sum_congr rfl fun _ _=>Finset.card_map _
variable [Fintype α] [Fintype ι] -- need instances BEFORE record list? fty FinSet complete implicit
lemma legend (t:Finset α) (p : Cl Md H): (p₁) p∈ ledger M H Z ℓ k (t.map σ)↔p∈ ledger Md H Z ℓ k t:= by
   unfold ledger; rw [mem_filter,mem_filter]; apply and_congr
   · rw [Stowe.posted,Stowe.posted]; rfl
   unfold struck Yielding; rw [accord,readable,Finset.card_map]; refine and_congr (and_congr ⟨fun h=>Finset.map_injective _ h,fun h=>congr_arg (Finset.map σ) h⟩ Iff.rfl) ?_
   change (∀ i,(peeled M σ (p.2 i).2).reach ⊆ (p.2 i).1.val) ↔ _
   simp_rw [fun i=> (tips M σ (p.2 i).2).1]
lemma enlargement : ledger M H Z ℓ k (s'.map σ)= (ledger Md H Z ℓ k s').map (p₁):= by
   ext x; constructor
   · intro h; obtain ⟨j,rfl⟩:=acres M H σ s' x (mem_filter.mp h|>.2.1.1.le); exact mem_map_of_mem _ ((legend M H Z σ s' j).1 h)
   intro h; obtain ⟨i,hi,rfl⟩:= mem_map.mp h; exact (legend M H Z σ s' i).2 hi
omit [Fintype α] [Fintype ι] in
lemma glasP (V:Config G c) : glass M g χ (p₁ p) V=glass Md (g ∘ σ) χ p V:= by
   unfold glass Gas.term; have he : coefficient (seam M H) (p₁ p).2 = coefficient (seam Md H) p.2:= Meadow.movement _ _ _ _ (fun _ _=> Iff.rfl)
   rw [he]; apply congr_arg (fun x=>_*x/_); refine Finset.prod_congr rfl (fun i _=>?_); change part _ _ _ ((p.2 i).1,peeled M σ (p.2 i).2) V= _
   unfold part; rw [show Palette.team M _= Palette.team (Md) (p.2 i).2 from (tips _ _ _).2]; exact congr_arg (fun x=>x*_) (Finset.prod_map ..)

lemma picture (ℓ k:ℕ)(a b: α→ℝ)(hv: g ∘ σ =a*b): tale M g H Z ℓ k (s'.map σ) (χ:=χ)= (dilation s' a) • tale Md b H Z ℓ k s' (χ:=χ):= by
   ext x; unfold tale; rw [Stowe.enlargement M H Z σ s', Finset.smul_sum, Finset.sum_map]; apply congr_fun; refine Finset.sum_congr rfl (fun i hi=>?_); ext x
   rw [glasP M g H σ i x,hv, (drag Md a H b i x).1, defined Md a H s' i (mem_filter.mp hi|>.2.1)]; rfl
end iris
end Stowe
end YM.RGComparison01.Pledge
