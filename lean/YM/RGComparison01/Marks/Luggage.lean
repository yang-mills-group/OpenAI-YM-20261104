import YM.RGComparison01.Marks.Brick
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
namespace Luggage
open Foreman Checks Baked Palette Pillow Resin Season Ink Heron
open Switch Mallow Ovens OmitClusters Song Refrain Motion Stowe
variable {η:Type} (M:ι→Lotus.Leaf R)(g:ι→ℝ)(H:Cash W s μ L Q o C T R) (P':BudgetPoint)
    (D' : Ribbon R n) (g' : ι→ℝ)
local notation "ZA"=> Cl M H
local notation "Z"=> Drawing.cabinet H D'
-- preserve true Crew choices.Lens
abbrev long (i:ι) := ∃ j,(M i).turn=Wing.logKey j∧¬D'.keep j
local notation "Ft"=> origins M H
variable [Fintype ι]
-- Y.Mark global preserving choice projector.DEM any copy bound; no implicit Leg collapse
abbrev Clear (p:Cl M H) := Season.allot p=(recordSet M H p).card
abbrev core (m:ℕ) (p:Cl M H) := (recordSet M H p).Nonempty ∧ Season.allot p ≤ m ∧ Clear M H p
def miss (m ℓ k:ℕ)(p:ZA):= core M H m p∧p∉ ledger M H (Drawing.cabinet H D') ℓ k (recordSet M H p)
-- Packet currency after read.With.V
section currency
variable (h:Rooted (origins M H) (glass M (g'*g) χ) P' a w)
local notation "g₀"=> Stowe.densityP M g' H
variable (X:Cl M H→Prop)(B : ℝ) (hp : Rooted (origins M H) (Checks.treat (χ:=χ) (ρ:=g'*g) (fun i=> X i)) P' a w)
include hp
omit [Fintype ι] in
lemma shrink (Φ:ZA→Prop)(hf:0< B)(he: ∀ i,Φ i → X i∧ B ≤ g₀ i) : Rooted Ft (Checks.treat (χ:=χ) (ρ:=g) Φ) P' a (B⁻¹*w):=by
   let f (x:ZA):=if Φ x then (g₀ x)⁻¹ else 0
   have hf :∀ i, |f i| ≤ B⁻¹:= by
     intro i; unfold f; split
     next hz=> have h:= (he i hz).2; rw [abs_of_pos (inv_pos.mpr (hf.trans_le h))]; exact inv_anti₀ hf h
     next=> rw [abs_zero]; exact inv_nonneg.mpr hf.le
   have ht:=hp.scales f hf (inv_pos.mpr (by assumption : 0<B)).le; convert ht using 1; ext i V; unfold Checks.treat f; split
   next hz=> rw [if_pos (he i hz|>.1)]; change _= (g₀ i)⁻¹*glass M (g'*g) χ i V; rw [(drag M g' H g i V).1, inv_mul_cancel_left₀ (by apply ne_of_gt; exact lt_of_lt_of_le ‹0<B› (he i hz|>.2))]
   next hv=> rw [zero_smul]
omit hp
end currency
variable (Ω : ℕ→Prop)
local notation "hTray"=>glass M (g'*g) χ
local notation "h₁"=> Checks.treat (χ:=χ) (ρ:=g'*g)
local notation "Hb"=> (fun i:Cl M H=>Season.Heavy k i∧¬Ode Ω i)
variable (hA : Rooted (origins M H) (glass M (g'*g) χ) P' a w)
    (hY: Rooted (origins M H) (Checks.treat (χ:=χ) (ρ:=g'*g) (fun i=>Season.Heavy k i∧ ¬Ode Ω i)) P' a A)
    (hΩ : Rooted (origins M H) (Checks.treat (χ:=χ) (ρ:=g'*g) (Ode Ω)) P' a K)
    (hx :∀ i,1≤g' i) (hl : ∀ i,Luggage.long M D' i→ δ≤g' i) (hB : 0<δ)
    (hQ:Drawing.Opens D' Ω)
local notation "Wt"=> Checks.treat (χ:=χ) (ρ:=g)
include hx hA
omit [Fintype ι] in
lemma full : Rooted (origins M H) (glass M g χ) P' a w:= by
   have h:Rooted (origins M H) (Checks.treat (χ:=χ) (ρ:=g'*g) (fun _=>True)) P' a w:= by unfold treat; simp_rw [if_true]; exact hA
   have ht:= shrink M g H P' g' (fun _=>True) 1 h (fun _=>True) zero_lt_one (fun z _=>⟨trivial,one_le_prod fun _ _=>one_le_prod fun i _=>hx i⟩)
   unfold treat at ht; simp only [if_true,inv_one,one_mul] at ht; exact ht
include hY hΩ hl hB hQ
lemma profits (m:ℕ)(q:ℝ)(hq : 0<q) : ∀ᶠ i in atTop,
    Rooted (origins M H) (Checks.treat (χ:=χ) (ρ:=g) (miss M H D' m (k+m) i)) P' a (K+A+δ⁻¹*w + q):=by
   let F :=Luggage.miss M H D' m (k+m)
   let C z := recordSet M H z
   let X z:= ∃ i∈ C z,Luggage.long M D' i
   have hv (z:ZA): 1 ≤ densityP M g' H z:= one_le_prod fun _ _=> one_le_prod fun i _=> hx i
   let f0 (i:ℕ) z:= Checks.treat (χ:=χ) (ρ:=g) (fun z:ZA=> F i z ∧ Ode Ω z) z
   let f1 (i:ℕ) z:= Checks.treat (χ:=χ) (ρ:=g) (fun z:ZA=> F i z ∧ Hb z) z
   let f2 (i:ℕ) z:= Checks.treat (χ:=χ) (ρ:=g) (fun z:ZA=> F i z ∧ X z ∧ ¬Hb z∧¬Ode Ω z) z
   let f3 i (z:ZA):= F i z∧¬X z∧¬Hb z∧¬Ode Ω z
   have hh z (hp:glass M g χ z≠0) : ∀ᶠ i in atTop,¬ f3 i z:= by
     by_cases H₀: core M H m z∧¬ X z∧¬Hb z∧¬ Ode Ω z; swap
     · refine Eventually.of_forall fun i hx=> H₀ ⟨hx.1.1,hx.2⟩
     obtain ⟨y,hy⟩:∃ V: Config G c,glass M g χ z V ≠0:= not_forall_not.mp (fun hx=> hp (funext fun i=> not_not.mp (hx i)))
     refine (Stowe.lowRibbon M g H (C z) z D' Ω hQ ?_ y ⟨rfl,H₀.1.2.2⟩ hy (fun h=>H₀.2.2.1 ⟨h,H₀.2.2.2⟩) H₀.2.2.2 m ?_).mono (fun i hi hx=> hx.1.2 hi)
     · intro j hj i hz; exact Classical.byContradiction (fun h=> H₀.2.1 ⟨j,hj,i,hz,h⟩)
     exact (H₀.1.2.2.symm.trans_le H₀.1.2.1)
   have hl' := (full M g H P' g' hA hx).fadings f3 hh hq
   filter_upwards [hl'] with i hi
   have h0 : Rooted Ft (f0 i) P' a K:= by simpa only [inv_one,one_mul] using (shrink M g H P' g' (Ode Ω) 1 hΩ (fun z=> F i z ∧ Ode Ω z) zero_lt_one (fun z hz=> ⟨hz.2,hv _⟩))
   have h1 : Rooted Ft (f1 i) P' a A:= by simpa only [inv_one,one_mul] using (shrink M g H P' g' Hb 1 hY (fun z=> F i z∧ Hb z) zero_lt_one (fun z hz=> ⟨hz.2,hv _⟩))
   have h2 : Rooted Ft (f2 i) P' a (δ⁻¹*w):= by
     apply shrink M g H P' g' (fun _=>True) _ _ _ hB; swap; · unfold treat; simp_rw [if_true]; exact hA
     rintro z ⟨hp,⟨j,hj,hK⟩,-,-⟩; refine ⟨trivial,(hl j hK).trans ?_⟩; rw [defined M g' H (C z) z ⟨rfl,hp.1.2.2⟩]; unfold dilation; rw [← mul_prod_erase _ _ hj]; apply le_mul_of_one_le_right (zero_le_one.trans (hx j)) (one_le_prod (fun i _=> hx i))
   convert h0.sumBudgetR h1|>.sumBudgetR h2|>.sumBudgetR hi using 1
   ext x V; by_cases hn:F i x; swap
   · have he:¬ miss M H D' m (k+m) i x:= hn
     simp only [f0,f1,f2,f3,Pi.add_apply,treat,hn,he,false_and,↓reduceIte,Pi.zero_apply,add_zero]
   have he:miss M H D' m (k+m) i x:= hn
   by_cases HX: Ode Ω x; · simp only [f0,f1,f2,f3,Pi.add_apply,treat, hn, HX, he, not_true, ↓reduceIte, Pi.zero_apply, and_false,and_true,add_zero]
   by_cases ht:Season.Heavy k x <;> by_cases hv:X x <;> simp only [Pi.add_apply,treat,f0,f1,f2,f3, ht,HX,not_false_eq_true,hv,hn,he,↓reduceIte,Pi.zero_apply,and_true,and_false,not_true,zero_add,add_zero]
end Luggage
end YM.RGComparison01.Pledge
