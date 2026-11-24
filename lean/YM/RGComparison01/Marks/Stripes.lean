import YM.RGComparison01.Marks.Creature
import YM.RGComparison01.Marks.Mood
/-!
# Attachment assembly. At real mark radii.

 Whereas M4 averages under all orientations, DON'T symmetrize any marks
 here! Only blank soft slots may be permuted. Arc lifts in Switch.Paid
 pass pointwise. -/
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
abbrev spot (w Y:ℕ):= Finset.univ.filter (Diner.Driver.Quick M E D S w Y)
local notation "Z₁"=> (Drawing.cabinet H E)
local notation "Qr"=> Diner.Driver.primary M D S
local notation "ZA"=> Cl M H
local notation "Zc"=> spot (S:=S) M D E w Y
local notation "Ft"=> origins M H
local notation "Φ"=> Ink.yielded M g H (χ:=χ)
variable (w ℓ k Y : ℕ)
local notation "Z'"=> ledger M H Z₁ ℓ k
abbrev floor (x:Site c) := (spot (S:=S) M D E w Y).filter fun p=> Qr p=x
def region (x:Site c) : Finset (Cl M H) := (floor (S:=S) M D E w Y x).biUnion (ledger M H Z₁ ℓ k)
-- whole relocated set. Card bound before healing
abbrev ballot : Finset (Cl M H):= (spot (S:=S) M D E w Y).biUnion (ledger M H Z₁ ℓ k)
lemma glint (z:Cl M H)(hp:Luggage.core M H w z)(he: z∈ledger M H Z₁ ℓ k (recordSet M H z))(h:Cabinet.garage (Deck.Mint.width Q.halo (radiusB s) (radiusB s+n)) ℓ≤Y): z∈ Stripes.ballot M D E H w ℓ k Y:= by
   refine mem_biUnion.mpr ⟨_, mem_filter.mpr ⟨mem_univ (recordSet M H z),?_⟩,he⟩; exact Diner.Driver.journeys H M E D (recordSet M H z) hp.1 (hp.2.2 ▸ hp.2.1) he h
lemma cargo (p:Finset ι)(hp:p∈ spot (S:=S) M D E w Y)(z:ZA) (hz:z∈ Z' p): core M H w z ∧ p=Stowe.recordSet M H z ∧ Qr p∈ origins M H z ∧ origins M H z⊆ neighbors (Cabinet.garage (Deck.Mint.width Q.halo (radiusB s) (radiusB s+n)) ℓ) (Qr p):= by
   have he := (mem_filter.mp hz).2; have hQ : Quick M E D S w Y p:= (mem_filter.mp hp).2
   have hv:= traits M H Z₁ p (Qr p) (main p hQ.1) (main p hQ.1).property (full_card M D S _ hQ.1) z hz
   exact ⟨⟨he.1.1.symm ▸ hQ.1,he.1.2.trans_le hQ.2.1, he.1.2.trans (congr_arg card he.1.1.symm)⟩, he.1.1.symm,hv⟩
lemma sitting (x:Site c) (z:ZA)(hz:z∈region M D E H w ℓ k Y x): let p:=Stowe.recordSet M H z; Luggage.core M H w z∧ p∈ spot (S:=S) M D E w Y∧ z∈ ledger M H Z₁ ℓ k p ∧ Qr p=x := by
   obtain ⟨p,hp,hz⟩:= mem_biUnion.mp hz; have he:=mem_filter.mp hp; obtain ⟨h,rfl,_,_⟩:= cargo M D E H w ℓ k Y p he.1 z hz; exact ⟨h,he.1,hz,he.2⟩
local notation "Yr"=> region M D E H w ℓ k Y
abbrev Tour := Finset ι → Config G c → ℝ -- address offering
abbrev amber (V Q : Tour (ι:=ι) (G:=G) (c:=c)) (p:Finset ι): Config G c→ℝ:= (Stowe.dilation p g) • V p + Q p
-- arbor: kernel per p. Spot ONLY. after Z masking.
def arbor (Z:ℕ) (P:BudgetPoint)(V W : Tour (ι:=ι) (G:=G) (c:=c)) (p:Finset ι)(U:Config G c): Ways ι:= if p∈ spot (S:=S) M D E w Y then Switch.click p (masked P.threshold (neighbors Z (Qr p)) (amber g V W p) U) else 0
-- soft at site.first union. Keep point-cont CPS.On.P
abbrev fog (Z:ℕ)(P:BudgetPoint)(x:Site c)(V:Config G c)(t:ℝ)(p:Finset ι): ℝ:= if Healthy P.threshold (neighbors Z x) V then 0 else ∑ z∈ Stripes.region M D E H w ℓ k Y x, Ink.yielded M g H z V t p (χ:=χ)
variable (Z : ℕ)(P' : BudgetPoint) (V Wp:Tour (ι:=ι) (c:=c) (G:=G))
variable (hp : ∀ z:Cl M H,pottery M g χ z=masked P'.threshold (origins M H z) (glass M g χ z))
  (hV:∀ p ∈ spot (S:=S) M D E w Y,∀ U,Healthy P'.threshold (neighbors Z (Diner.Driver.primary M D S p)) U → Stowe.tale M g H (Drawing.cabinet H E) ℓ k p U (χ:=χ) =Stowe.dilation p g * V p U+ Wp p U)
  (hf : Cabinet.garage (Deck.Mint.width Q.halo (radiusB s) (radiusB s+n)) ℓ ≤ Z)
local notation "U'"=> arbor (S:=S) M g D E w Y Z P' V Wp
local notation "Zt"=> region M D E H w ℓ k Y
lemma melt (p:Finset ι)(hp:p∈ spot (S:=S) M D E w Y)(U:Config G c)(t:ℝ)(J:Finset ι): ∑ z∈ledger M H Z₁ ℓ k p, Ink.yielded M g H z U t J (χ:=χ)= Switch.click p (Stowe.ship M g H Z₁ ℓ k p U (χ:=χ)) t J:= by
   have he:p.Nonempty:= (mem_filter.mp hp).2.1
   unfold Stowe.ship; rw [Finset.sum_congr rfl (fun i (_:i∈ ledger M H Z₁ ℓ k p)=> congr_fun (congr_fun (Stowe.code M g H p i (χ:=χ) (mem_filter.mp (by assumption : i∈ ledger M H Z₁ ℓ k p)|>.2.1) he U) t) J)]; unfold Switch.click; split_ifs; rw [Finset.mul_sum]; simp only [sum_const_zero]
lemma stashed (x:Site c)(U:Config G c)(t:ℝ)(p:Finset ι):
    ∑ z∈ region M D E H w ℓ k Y x, yielded M g H (χ:=χ) z U t p= ∑ i∈ floor (S:=S) M D E w Y x, Switch.click i (Stowe.ship M g H Z₁ ℓ k i U (χ:=χ)) t p := by
   unfold region; rw [Finset.sum_biUnion]
   · apply Finset.sum_congr rfl; intro i hp; exact melt M g D E H w ℓ k Y i ((mem_filter.mp hp).1) U t p
   rintro i hi j hj hz; apply Finset.disjoint_left.mpr; intro u hq h'; exact hz (((cargo M D E H w ℓ k Y i ((mem_filter.mp hi).1) u hq).2.1).trans (((cargo M D E H w ℓ k Y j ((mem_filter.mp hj).1) u h').2.1).symm))
include hp hV hf
lemma enters (x:Site c)(U:Config G c)(t:ℝ)(p:Finset ι): (∑ z∈region M D E H w ℓ k Y x, yielded M g H (χ:=χ) z U t p) = (∑ i∈floor (S:=S) M D E w Y x,U' i U t p) + fog M g D E H w ℓ k Y Z P' x U t p (χ:=χ) := by
   by_cases ht:Healthy P'.threshold (neighbors Z x) U
   · rw [fog, if_pos ht, add_zero,stashed]; refine sum_congr rfl fun i hi=> ?_
     obtain ⟨hi,hx⟩:=mem_filter.mp hi; have hy: Healthy P'.threshold (neighbors Z (Qr i)) U:=hx.symm ▸ ht; have he : i.Nonempty:= (mem_filter.mp hi).2.1
     have hz:= standing M g H Z₁ P'.threshold hp i (Qr i) (main i he) (main i he).property (full_card M D S i he) U (k:=k) (ℓ:=ℓ) (hy.mono_left (fun i hi=> (neighbors_mem ..).2 (((neighbors_mem ..).1 hi).trans hf)))
     rw [hz,hV i hi U hy,arbor,if_pos hi,masked_eq _ _ _ _ hy]; rfl
   rw [fog,if_neg ht, Finset.sum_eq_zero (f:=fun i=> U' i U t p),zero_add]; intro i hi; obtain ⟨hv,h⟩:=mem_filter.mp hi; rw [arbor,if_pos hv,h,masked_ne _ _ _ _ ht]; simp [Switch.click]
lemma exhibit (U:Config G c)(t:ℝ)(p:Finset ι):
    (∑ z∈ Stripes.ballot M D E H w ℓ k Y, Ink.yielded M g H z U t p (χ:=χ))= (∑ i,U' i U t p)+ ∑ x:Site c, fog M g D E H w ℓ k Y Z P' x U t p (χ:=χ):=by
   let g' (x:Site c):=Zt x
   let F' x:=floor (S:=S) M D E w Y x
   have ht : univ.biUnion g' = ballot M D E H w ℓ k Y:= by
      ext z; unfold g' region ballot; simp only [mem_biUnion,mem_univ, true_and]; constructor
      · rintro ⟨x,p,hp,hz⟩; exact ⟨_,(mem_filter.mp hp).1,hz⟩
      rintro ⟨p,hp,hz⟩; exact ⟨Qr p,p,mem_filter.mpr ⟨hp,rfl⟩,hz⟩
   rw [←ht, Finset.sum_biUnion]
   · unfold g'; simp_rw [enters M g D E H w ℓ k Y Z P' V Wp hp hV hf _ U t p,sum_add_distrib]; congr 1
     rw [← Finset.sum_biUnion]; swap
     · intro x hx y hy hz; exact Finset.disjoint_left.mpr fun i h h'=> hz ((mem_filter.mp h).2.symm.trans ((mem_filter.mp h').2))
     refine sum_subset (subset_univ _) ?_; intro i hi hx; unfold arbor; rw [if_neg (show i ∉ spot (S:=S) M D E w Y from fun h=>hx (Finset.mem_biUnion.mpr ⟨Qr i,mem_univ _,mem_filter.mpr ⟨h,rfl⟩⟩))]; rfl
   intro x hx y hy hz; exact Finset.disjoint_left.mpr fun i h h'=> hz ((sitting M D E H w ℓ k Y x i h|>.2.2.2).symm.trans (sitting M D E H w ℓ k Y y i h'|>.2.2.2))
end Stripes
end YM.RGComparison01.Pledge
