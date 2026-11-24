import YM.RGComparison01.Marks.Stripes
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
namespace Stripes
open Diner
open Lanes Foreman Checks Baked Palette Pillow Resin Season Ink Heron Switch Mallow Ovens OmitClusters Song Refrain Motion Luggage Oceanic Extra.Iteration
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03 ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter PhysicalNext PhysicalNext.Repeat Deck Stellar Mint Greenbelt Boulevard Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration Song Refrain Reserves OmitClusters
open Divides Input Org Supply PriceCompiler Next.Scheduling Progress.DirectedRecipe Time Opera Slide
open Hoboken Stowe SliceRows
open Diner.Borders Diner.Driver
variable {w m K0 Y Z:ℕ}
variable (M:ι→Lotus.Leaf R)(g:ι→ℝ) (D:Driver M) (E:Ribbon R n)(H:Cash W s μ L Q o C T R)
variable [Fintype ι]
open Diner.Borders Diner.Driver Mood
variable (m ℓ k Y Z : ℕ)
local notation "Z₁"=> (Drawing.cabinet H E)
local notation "Qr"=> Diner.Driver.primary M D S
local notation "ZA"=> Cl M H
local notation "Zc"=> spot (S:=S) M D E m Y
local notation "Ft"=> origins M H
local notation "Φ"=> Ink.yielded M g H (χ:=χ)
local notation "Zt"=> region M D E H m ℓ k Y
variable (P' : BudgetPoint)
local notation "V'"=> fog M g D E H m ℓ k Y Z P' (χ:=χ)
-- All incoming support positions not just crest root, paid on every occurrence
lemma signsUp (i:ι) (x:Site c)(hp:x∈ H.supportP (Palette.sign M S i))(z:Site c)(hz:Y+2*Mint.width Q.halo (radiusB s) (radiusB s+n) ≤ Z) (hZ:x ∉ neighbors Z z) (t:ℝ)(p : Finset ι)(U:Config G c):
   fog M g D E H m ℓ k Y Z P' z U t p (χ:=χ)=fog M g D E H m ℓ k Y Z P' z U t (p.erase i) (χ:=χ):= by
   unfold fog; split; rfl
   refine Finset.sum_congr rfl fun j hj=>?_ ; have hh:= sitting M D E H m ℓ k Y z j hj; let u:= recordSet M H j; have ht: Quick M E D S m Y u:= (mem_filter.mp hh.2.1).2
   have hu: i∉u := fun hi=> hZ (by rw [← show Qr u=z from hh.2.2.2]; exact (neighbors_mem ..).2 (((neighbors_mem ..).1 ((creature M D E m Y u ht H i hi) hp)).trans hz))
   simp_rw [Stowe.code M g H u j ⟨rfl,hh.1.2.2⟩ ht.1 U (χ:=χ)]; unfold click; by_cases he:u⊆p
   · rw [if_pos he,if_pos (show u⊆p.erase i from fun y hy=>mem_erase.mpr ⟨fun h=> hu (h ▸ hy),he hy⟩)]
   rw [if_neg he,if_neg (fun h=> he (Subset.trans h (erase_subset ..)))] -- namespace
lemma fogHush (i:ι)(o:Site c)(hp:o∈ H.supportP (Palette.sign M S i))(hz:Y+2*Mint.width Q.halo (radiusB s) (radiusB s+n) ≤ Z) (X : Pipes G c)(Q: Tap G c) : Motion.Hush i o (Loft X Z).softer (Mood.rite Q V'):=by
   intro j t p hj; funext U; let e:= Mood.trade c
   change o∉ Mood.counsel X Z (e j) at hj
   change Mood.quip Q (fun o U=> V' o U t p) (e j) U=_; unfold Mood.rite; dsimp only [Function.comp_apply]; generalize hk : Mood.trade c j=z
   rw [show e j=z from hk] at hj; cases z with
   | inl i=>rfl
   | inr j=>exact signsUp M g D E H m ℓ k Y Z P' i o hp j hz hj t p U
-- strengthen per old ; Palette.acts
omit [Fintype ι] in
lemma rootAt (V:Config G c)(p:Molecule S) (X:Tickets (Palette.sign M S))(hx:Palette.act M H χ V p X≠0)(j:ι)(he:j∈ X.val) : H.supportP (Palette.sign M S j)⊆ H.unionP p:= by
   letI: Nonempty (Forest S.ratio):=Tree.select S.ratio S.patch.odd_side
   exact subset_biUnion_of_mem _ ((Palette.present M H χ V X p (F:=Classical.ofNonempty) hx).1 (X.reaches_of he))
variable (U:Config G c)(j:ι)(x:Site c) (he:x∈ H.supportP (Palette.sign M S j))
include he
lemma centers (i:Molecule S)(hz:x∉H.unionP i)(t:ℝ)(Z:Finset ι): Palette.vote M H χ g i U t Z=Palette.vote M H χ g i U t (Z.erase j):=by
  unfold Palette.vote Palette.color; apply sum_congr rfl; intro v _
  by_cases hv:j∈v.val
  · rw [show Palette.act M H χ U i v=0 from Classical.byContradiction (fun h=> hz (rootAt M H U i v h j hv he)),mul_zero,mul_zero]
  exact congr_arg (·*_) (prod_congr rfl fun i hi=> by unfold ways; simp_rw [show i∈Z.erase j↔ i∈Z from (mem_erase.trans (and_iff_right (fun h=>hv (h ▸ hi))))])
lemma mirror (i:H.fragrances)(hz:x∉H.bookFoot (.inr i)) (t:ℝ)(Z:Finset ι): Palette.song M H χ g i U t Z=Palette.song M H χ g i U t (Z.erase j):= by
  refine congr_arg (fun v:ℝ=> (coefficient H.seam i.2*v/↑(i.1+1).factorial)) (prod_congr rfl (fun p _=> ?_)); exact centers M g H U j x he (i.2 p).val (fun h=> hz (Finset.subset_biUnion_of_mem (H.smallAt ∘ i.2) (mem_univ p) h)) t Z
lemma castle (i:H.Chainbook)(hz:x∉H.library i)(t:ℝ)(Z:Finset ι): Palette.fete M H χ g i U t Z=Palette.fete M H χ g i U t (Z.erase j):=by
  unfold Palette.fete Cash.smilesMill; split
  next hx=>
    refine Finset.prod_congr rfl fun y _=> congr_arg (fun t:ℝ=> t^(i.2 y+1)/↑(i.2 y+1).factorial) ?_
    rcases y with ⟨i'|i',hv⟩
    · exact centers M g H U j x he i'.val (fun h=> hz (Finset.subset_biUnion_of_mem H.bookFoot hv h)) t Z
    exact congr_arg (- ·) (mirror M g H U j x he i' (fun h=>hz (Finset.subset_biUnion_of_mem H.bookFoot hv h)) t Z)
  rfl
variable (Γ : Match.Alliance H H 1 0)
local notation "X₀"=> (Beam.marquee H P')
lemma originHush : Motion.Hush j x (fun i=> ((X₀).hard i).support) (Palette.shoot M H χ g H Γ):=by
    intro i t z ht
    by_cases h: i∈Set.range (Refrain.visa H Γ)
    · obtain ⟨i,rfl⟩:=h; funext U; change x∉ (Refrain.reserve H (Refrain.badge H (Refrain.visa H Γ i))).support at ht
      unfold Palette.shoot Palette.shootK;rw [stuffed,stuffed]; exact castle M g H U j x he _ (fun h=>ht ((Refrain.admitted H Γ i).1.symm ▸ h)) t z
    unfold Palette.shoot Palette.shootK; rw [Progress.DirectedRecipe.blank _ _ h,Progress.DirectedRecipe.blank _ _ h]
omit he
omit [Fintype ι] in
lemma picture (z:Cl M H)(h: Pillow.glass M g χ z ≠0) (j:ι)(hp:j∈ recordSet M H z): H.supportP (Palette.sign M S j)⊆ origins M H z:= by
   obtain ⟨U,hU⟩:= not_forall_not.mp (fun hx=> h (funext (fun i=>not_not.mp (hx i)))) -- type fix
   obtain ⟨i,hi,hj⟩:= mem_biUnion.mp hp; have he:Pillow.part M g χ (z.2 i) U≠0:= fun ht=>hU (by unfold glass Gas.term; rw [prod_eq_zero hi ht,mul_zero,zero_div]; rfl) -- path
   have ht:= (Canyon.partOn U (z.2 i) he).2.2 ((z.2 i).2.reaches_of hj)
   exact Finset.Subset.trans (subset_biUnion_of_mem _ ht) (subset_biUnion_of_mem (raised M H ∘ z.2) hi)
end Stripes
end YM.RGComparison01.Pledge
