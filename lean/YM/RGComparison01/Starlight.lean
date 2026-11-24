import YM.RGComparison01.Cuprite.Opal
/-!
# Sell common masks: Restoration of actual Local with extras.

 Model part and regular discrepancy share basis, distinct ledgers; thus
 can consume termwise and/or split this basis at equal labels. No
 equality between norm of evaluations and offerings. K and penalty paid
 through attachment. -/

set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter
open PhysicalNext PhysicalNext.Repeat Deck Stellar Mint Greenbelt Boulevard Trio
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration Song Refrain Reserves OmitClusters
open Divides Input Org Supply PriceCompiler Next.Scheduling Progress.DirectedRecipe Time Opera Slide
open RG.Supply RG.Shoot Push.Uniform Sienna Pane
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
namespace Starlight
variable {G : Gauge} {X : Metals G} {D : Rolls X.p} {A : Alloy X D} (F : Roost.Factor A)
variable {c f : Side} {m n N k w b i K: ℕ} {Y : Stars→Side} {τ t u v p s' : ℝ}
variable (l : f.val=c.val*(A.B.a.S.block m).val) {R : RG.Rep G f}
    (H : Boulevard.Chartlet F.shape A N m l R) (Z : Ribbon R n)
local notation "Jp" => A.B.a.clock.J (m+1)
local notation "Ip" => A.B.a.clock.J m
local notation "x₀" => A.B.a.clock.hatBeta m
local notation "B" => A.B.a.budget m
local notation "K'" => A.B.a.budget (m+1)
local notation "W'" => Pane.orchestra A N l
local notation "T" => Pane.panel A m l
local notation "X₀" => Drawing.cabinet H Z
local notation "e" => (X.p.profile Ip)
set_option quotPrecheck false
local notation "E" => F.expense Jp Ip
local notation "g" => A.B.kin.alpha N m
local notation "Y'" => Beam.marquee H B
local notation "O" => Chi.canonical
local notation "P'" => plusone H (selfA H) O g
local notation "L₀" => D.L Jp
local notation "b₀" => Library.hall F m n K
local notation "b₁" => Cabinet.leftward (X₀) O g K i
local notation "C₀" => Time.forecastK A.B.a m F.scout R.beta
variable (Q : ∀ i:Stars,(Y i).val=2*(w+i.val)) (M₀ : Trio.Offer G c) (z:ℕ) (M U : ∀ i:Stars, Trio.Offer G (Y i))
local notation "Θ" => Trio.ornament (c:=c) Q (U-M)
local notation "u₀" => Cabinet.tot (X₀) O K i g - M₀

-- exact posting
-- use var sizes after hulls.
def hotB (Y : Stars→Side) (n:ℕ) (p c:ℝ) (p' : Stars→ℝ) := let x:=(ballCost n:ℝ)*c; x+p+(x+p)+ ∑ i:Stars,|Slide.ray i| * ((Fintype.card (Site (Y i)):ℝ)*(p' i+p' i))
-- Lens after split! book B.cost independent choice of κ by .hak
abbrev tap (K i : ℕ):=
   Marlin.bison (Cabinet.leftward (Drawing.cabinet H Z) O g K i) ((Θ)+M₀) (Purity.dispatch (Drawing.cabinet H Z) B K i g O Q z U M M₀)
abbrev book (z : ℕ):= Marlin.lodge (Beam.marquee H B) z (2*z)
local notation "X1" => (book F l H z)
local notation "P1" => (tap F l H Z Q M₀ z M U K i)
local notation "ℙ" => (Marlin.raiser B)
-- S budget on model *used for pay*, p at LEAP stable. B2 unaffected
section pro

variable (Y₀ : ℝ) (P : Stars→ℝ) {q : ℝ}
variable (hp : ∀ x,(A.B.a.budget m).Regular (neighbors z x) (M₀ x))
  (hV : M₀ ≠ Trio.ornament Q M → ∀ x,(A.B.a.budget m).supBounds x (neighbors z x) (M₀ x) p)
  (hs : ∀ i j, (A.B.a.budget m).Regular univ (M i j))
  (ht : ∀ i j,(A.B.a.budget m).Regular univ (U i j))
  (hV0 : M₀=Trio.ornament Q M→0≤p∧∀ i (y:Config G (Y i)),flags (A.B.a.budget m).threshold y=∅→∀ x, ‖U i x y‖≤ P i)
  (hz: M₀≠ Trio.ornament Q M→∀ i (y:Config G (Y i)), flags (A.B.a.budget m).threshold y=∅→∀ x, ‖(U-M) i x y‖≤ P i)
variable (hB: w+4≤z)

include hp hV hs ht hz hV0 hB
variable (hf : 4*Library.hall F m n K +16 ≤ c.val)
  (hk:2*Library.hall F m n K ≤ w) (hq : Boulevard.SeekR F.shape A N m l H)
    (hT: Trio.CompatibleP (A.B.a.budget m) (Library.hall F m n K) (Cabinet.tot (Drawing.cabinet H Z) O K i (A.B.kin.alpha N m)) U)
  (hM: M₀≠Trio.ornament Q M → Trio.CompatibleP (A.B.a.budget m) (Library.hall F m n K) M₀ M)
variable (hy : Collection.Local (Beam.marquee H (A.B.a.budget m)) (A.B.a.budget m) (plusone H (selfA H) Chi.canonical (A.B.kin.alpha N m)) Y₀ (Coin.wage F m))
   (hδ: Collection.Local (Beam.marquee H (A.B.a.budget m)) (A.B.a.budget m) (Cabinet.leftward (Drawing.cabinet H Z) O (A.B.kin.alpha N m) K i) τ (Coin.wage F m))
   (hC: ∀ i : Site c,(coverNumber (A.B.a.budget m).B (neighbors (2*z) i):ℝ)≤ v) (hκ: Payments.Rates (A.B.a.budget m).B (Time.forecastK A.B.a m F.scout R.beta) (Coin.wage F m) (Marlin.tithe (2*z) (hotB Y (Library.hall F m n K) p Y₀ P) (A.B.a.budget m) v) q)
include hC hκ hδ hy hf hk hq hT hM
lemma trade : Ingredients (X1) (Marlin.dummy P1) (ℙ) 0 C₀ := by
  have hR:=Rain.jersey (A:=A) (m:=m)
  have hx : (B).supportExponent+3≤ (E).earn:= by rw [hR.2.2.1]; exact F.pledging.agenda _ _ (step_paid A.B.a m)|>.1
  obtain ⟨K₁,hK,hG⟩:= Refrain.chargesOut (ℙ) H (Divides.selfA H) O hq rfl (by change (B).supportExponent+1+1≤_; linarith only [hx])
  apply Marlin.stakes (B) Y' z (2*z) b₁ _ _ hδ.family hδ.transforms hκ (show ∀ i,_ from hK) hG _ _ _ hC (le_refl _)
  · exact fun i'=> Purity.mile _ _ _ _ _ _ _ _ _ _ _ hy rfl hk hB hp ht hs _
  · intro i' V he hx'; exact he (Purity.irritable _ _ _ _ _ _ _ _ _ _ _ rfl hk hB _ hf hT hM _ hx')
  exact fun i V => Purity.salary _ _ _ _ _ _ _ _ _ _ _ hy rfl hB _ P hV0 (fun hx=>⟨hV hx,hz hx⟩) _
end pro

-- after Proof sibling
abbrev sold (K i : ℕ) := Marlin.poursP (B) X1 (tap F l H Z Q M₀ z M U K i)
abbrev paper := Marlin.pluck B (book F l H z)
abbrev Title := (Sum.elim (fun _:ℕ=> (0:Config G c→ℝ)) (Song.choir M₀) ∘ Marlin.leanU c)
abbrev Part (K i : ℕ):ℕ→ Config G c→ℝ := Sum.elim (Cabinet.leftward (X₀) O g K i).logRead (Song.choir (Θ)) ∘ Marlin.leanU _
local notation "t₁" => Title M₀
local notation "u₁" => Part F l H Z Q M U K i
local notation "S₁" => sold F l H Z Q M₀ z M U K i
local notation "P₁" => paper F l H z

lemma traced : (S₁).logRead=t₁+u₁:= by
  let f:= ((Θ)+M₀)
  funext j
  change Sum.elim _ _ (Marlin.leanU c j)= (Sum.elim (fun _=>0) (Song.choir M₀) (Marlin.leanU c j)) + (Sum.elim (b₁).logRead (Song.choir Θ) (Marlin.leanU c j))
  cases Marlin.leanU c j with
  | inl i=> change _=(0:Config G c→ℝ)+_; rw [zero_add]; rfl
  | inr i=>change choir f _= _; funext V; change Rim c* f _ (i.1.view V)= Rim c * M₀ i.2 _+ Rim c * Θ _ _; unfold f; simp only [Pi.add_apply]; ring

lemma loaf (W:Trio.Offer G c) (p:ℝ) (hw : ∀ i,(B).Regular (neighbors z i) (W i)) (hf : ∀ i,(B).supBounds i (neighbors z i) (W i) p) (hV : ∀ i : Site c,(coverNumber (B).B (neighbors z i):ℝ) ≤ v): Meadow.Budget B (Marlin.leap z) W (p* Real.exp (preExponent B *v)):= by
  refine ⟨fun _=>p,fun i=>?_,fun i=> ⟨hw i,hf i⟩⟩; apply budget_finite
  · intro j; split; exact mul_nonneg (hf j|>.1) (Real.exp_nonneg _); rfl
  rw [Finset.sum_eq_single i]; rw [if_pos (show (Marlin.leap z i).site=i from rfl)]
  · exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_left (hV i) (headline B|>.exponent_pos.le))) (hf i|>.1)
  · intro j hj he; exact if_neg he
  simp

variable {Y₀:ℝ}
variable (hp : ∀ x,(A.B.a.budget m).Regular (neighbors z x) (M₀ x))
  (hV : ∀ x,(A.B.a.budget m).supBounds x (neighbors z x) (M₀ x) p)
  (hs : ∀ i j, (A.B.a.budget m).Regular univ (M i j))
  (ht : ∀ i j,(A.B.a.budget m).Regular univ (U i j))
variable (hB: w+4≤z)
variable (hy : Collection.Local (Beam.marquee H (A.B.a.budget m)) (A.B.a.budget m) (plusone H (selfA H) Chi.canonical (A.B.kin.alpha N m)) Y₀ (Coin.wage F m))
   (hδ: Collection.Local (Beam.marquee H (A.B.a.budget m)) (A.B.a.budget m) (Cabinet.leftward (Drawing.cabinet H Z) O (A.B.kin.alpha N m) K i) τ (Coin.wage F m))
   (hC: ∀ i : Site c,(coverNumber (A.B.a.budget m).B (neighbors (2*z) i):ℝ)≤ v)
variable (hr:∀ i:Site c,(A.B.a.budget m).supBounds i (neighbors z i) (Trio.ornament (c:=c) Q (U-M) i) s')
local notation "p₂" => turnFee B*(s'*Real.exp (preExponent B*v))
local notation "p₁" => turnFee B*(p * Real.exp (preExponent B*v))
include hp hV hs ht hδ hC hr hB
lemma regional : Meadow.Budget B (P₁).reg t₁ p₁ ∧ Meadow.Budget B (P₁).reg u₁ (τ+p₂) := by
  have ht' : ∀ i : Site c,(coverNumber (B).B (neighbors z i):ℝ) ≤ v:= by
    intro i; apply le_trans ?_ (hC i); exact_mod_cast (Corona.cover_mono (show neighbors z i⊆neighbors (2*z) i from fun i hi=> (neighbors_mem ..).2 (((neighbors_mem ..).1 hi).trans (by omega))) (B).B)
  let S' : Collection.Source G c:= ⟨0,0⟩
  have hf : Meadow.Budget B (Y').reg S'.logRead 0 := by refine ⟨fun _=>0,fun i=> ?_,fun i=> ⟨CouplingShape.reg_const _, VerifiedReset.sup_le (CouplingShape.sup_const _) abs_zero.le⟩⟩; simp [SumBudget]
  have ht₁ := Marlin.reg_bison Y' z (2*z) S' M₀ M₀ hf (loaf z M₀ p hp hV ht')
  obtain ⟨f,h,hY⟩:= hδ.cheap
  have ht₂ := Marlin.reg_bison Y' z (2*z) b₁ Θ Θ (show Meadow.Budget B (Y').reg (b₁).logRead τ from ⟨_,hY,fun i=> ⟨hδ.smooth i,h i⟩⟩) (loaf z Θ s' (Purity.holy B Q z U M hB ht hs) hr ht')
  rw [zero_add] at ht₁; exact ⟨ht₁,ht₂⟩

include hy
lemma reconstruct (hm: Ingredients (X1) (Marlin.dummy P1) (ℙ) 0 C₀) (he:M₀≠Trio.ornament Q M→Trio.Mirrors M₀):
    Collection.Local (P₁) B (S₁) (p₁+(τ+p₂)) C₀ ∧ ∀ v:ℝ,earlyValue Y' (W').down (W').low B P' R.beta v g =
      earlyValue (P₁) (W').down (W').low B (S₁) R.beta (v-u₀ 0 1) g := by
  obtain ⟨ht₁,ht₂⟩:=regional F l H Z Q M₀ z M U hp hV hs ht hB hδ hC hr
  have hS: Meadow.Budget B (P₁).reg (S₁).logRead (p₁+(τ+p₂)):= by rw [Starlight.traced]; exact Ports.budgetS ht₁ ht₂
  have hR:= Marlin.sous hm hS (fun s b=> Marlin.reeds _ _ _ _ _ _ _ _ (hδ.transforms s b|>.some)); refine ⟨hR,fun v=> funext fun V=>?_⟩
  obtain ⟨f,hF,h⟩:= hδ.cheap
  exact Marlin.carries B Y' z (2*z) b₁ ((Θ)+M₀) _ V (P') (fun _=>⟨rfl,rfl⟩) _ _ _ _ _ _ hm (show Meadow.Budget B (Y').reg (b₁).logRead τ from ⟨_,h,fun i=> ⟨hδ.smooth i,hF i⟩⟩) (Purity.pressed _ _ _ _ _ _ _ _ _ _ _ hy he) hy.transforms hδ.transforms
end Starlight
end YM.RGComparison01
