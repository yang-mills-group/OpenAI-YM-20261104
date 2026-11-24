import YM.FormalBulk08.Borough.Purchase
import YM.FormalBulk08.Dove.Pulse
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Borough
open Lattice Laurent Bloch Precision Stationary RG Wilson Filter Function
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix
open Next.Free Reef Flat Dove Dove.Lab North Elm Spigot Aster Source Drops Labels
open RG.Supply Push.PriceCompiler
variable {X:Type}{G:Gauge}{K:KernelChoices}{W:Borough.Window G K}{F:∀ d,Frame G d}{H:Hol G}{ρ:ChartRatio G}{Q:Herald}{Y:Sheet G}{P:Rolls Y}{T:Protection P}{V:Delays T}{M:Bar V}{B:Wait M}{A:Levels G}
-- global hatted-age convention use on fine tail
-- implementation w max 1. exact on Evergreens.
def lyre (A:Levels G): Time ℕ:= ⟨fun i =>max 1 (ageZ (A.clock.hatBeta i)),fun _=>le_max_left ..⟩
lemma measure (h:Evergreens K Q F H ρ W A)(i): (lyre A).day i = ageZ (A.clock.hatBeta i):= max_eq_right (progZ (h.beta i))
def register (G:Gauge)(K:KernelChoices)(U:Empire G K X)(Y:Borough.Window G K)(k:X→ℕ)(T:X→Time ℕ): Lab G K X:= ⟨U,T,k,fun x=> Y.width ∘ (U.V x).clock.J⟩
variable {U:Empire G K X}{X₀:X→ℕ}
-- no assumptions on widths carried into combination UFO age.
section
variable (hG:G.Simple)(hp:∀ i,Evergreens K Q F H ρ W (U.V i))(k:X→ℕ)
omit hG in
lemma across (hp:∀ i,Evergreens K Q F H ρ W (U.V i)): Soft (chron (register G K U W k (fun i=>lyre (U.V i))).scrolls) (fun i=> (wideA i:ℝ)):= by
   refine ⟨1,1,zero_le_one,fun x=>?_⟩; have he:=hp x.a; obtain ⟨B,b,P,h⟩:=he.payment x.b; rw [pow_one,one_mul]; change |(((U.V x.a).S.block x.b).val:ℝ)|≤ (lyre (U.V x.a)).day x.b; rw [measure he x.b]; simp only [Nat.abs_cast]; exact h.1.trans P
include hG hp
lemma supply_lyre : Years (register G K U W k (fun i=>lyre (U.V i))).scrolls:= by
   refine ⟨⟨1+G.slopeConstant,add_nonneg zero_le_one (Gauge.slopeConstant_pos hG).le, fun x n i _ h=>?_⟩,across k hp⟩
   obtain ⟨hs,hx,ht⟩:= ages G (U.V x) hG (hp x).beta h
   change (lyre _).day _≤ _*((lyre _).day _+ sowing (U.V x).S _ _); rw [measure (hp x),measure (hp x)]; refine ht.trans ?_
   nlinarith only [sowing_plus (U.V x).S h, hs,Gauge.slopeConstant_pos hG]
omit k hG in
lemma can_bill (T:X→Time ℕ)(k:X→ℕ)(hb:Years (register G K U W k T).scrolls)(hs:Soft (chron (register G K U W k T).scrolls) (fun i=>ageZ ((U.V i.a).clock.hatBeta i.b)) )(J:ℕ)(h:5≤J)(hr:∀ x,J≤ (U.V x).clock.J (k x+1)) :
    let Y:=register G K U W k T
    Avenue.Extras Y ∧ Soft (chron Y.scrolls) (fun i=>(Y.windowD i)⁻¹) ∧ ∀ E ≤ J, Y.Use ρ E ∧ Broc.Render Y E ∧∀ d D, d+3 ≤ J → d< D→D ≤ J→∀ (o:Loc G 1) (R:ℕ), R≤J→Quota (F d) H Y o D E R ∧∀ l≤ J,∀ u≤ J, VividC u o E D l Y Q:= by
    intro Y
    have hT (i:Leaf Y.scrolls): J≤Y.upper i:= (hr i.a).trans ((U.V i.a).fits.mono (show k i.a+1 ≤ i.b+1 from Nat.add_le_add_right i.zone _))
    have hx (i:Leaf Y.scrolls): Y.lower i ≤ Y.upper i:= (Y.V i.a).fits.mono (Nat.le_add_right ..);have hv (i:Leaf Y.scrolls): Y.upper i≤ Y.lower i+1:= (Y.V i.a).fits.stepSlow _
    let f (i: Leaf Y.scrolls):=ageZ ((U.V i.a).clock.hatBeta i.b); choose C hC hc S using fun i:Leaf Y.scrolls=> (hp i.a).payment i.b
    have hi i:C i≤|f i|:= (hc i).trans (le_abs_self _)
    have hz i:=W.lines (hx i) (hv i)
    refine ⟨hs.below fun i=>?_,hs.below fun i=> ?_,fun E hE=>?_⟩
    · exact (le_add_of_nonneg_left (abs_nonneg _)).trans (((S i).header _ (hx i)).trans (hi i))
    · exact (le_add_of_nonneg_right (abs_nonneg _)).trans (((S i).header _ (hx i)).trans (hi i))
    have hy i:= (S i).coarse _ (hx i) E (hE.trans (hT i)); have hQ (i:Leaf Y.scrolls): (((U.V i.a).clock.factor (Y.upper i)).val:ℝ)= wideA i:=by
       dsimp only [upper]; rw [show Y.V i.a=U.V i.a from rfl,(U.V i.a).fits.sameFactor];rfl
    refine ⟨⟨hb,fun i=> h.trans (hT i),fun i=>W.pos _,fun i=>(hz i).1,fun i=>(hz i).2.1,fun i=> ((hp i.a).pre.vacuum _ _ _ (hE.trans (hT i)) (hx i) (hv i)).trans_eq (hQ i),hs.below fun i=>?_,hs.below fun i=>?_⟩,⟨hs.below fun i=> ?_,hs.below fun i=>?_⟩,fun d D hd ht hD o R hr=>?_⟩
    · exact ((S i).past _ (hx i) E (hE.trans (hT i)) _ (Y.wood i.a i.b) rfl rfl).trans (hi i)
    · exact ((le_add_of_nonneg_right (abs_nonneg _)).trans (le_add_of_nonneg_right (abs_nonneg _))).trans ((hy i).trans (hi i))
    · exact ((le_add_of_nonneg_left (abs_nonneg _)).trans (le_add_of_nonneg_right (abs_nonneg _))).trans ((hy i).trans (hi i))
    · exact (le_add_of_nonneg_left (add_nonneg (abs_nonneg _) (abs_nonneg _))).trans ((hy i).trans (hi i))
    have ht' i:= (ht.le.trans hD).trans (hT i); refine ⟨⟨ht,fun i=>by have := hd.trans (hT i);omega,fun i=> (hz i).2.2,fun i=> ((hp i.a).pre.fields _ _ _ _ _ _ o (ht' i) (hD.trans (hT i)) (hE.trans (hT i)) (hr.trans (hT i)) (hx i) (hv i)).trans_eq (hQ i),hs.below fun i=>?_⟩,fun l hl u hu=>?_⟩
    · exact ((S i).light _ (hx i) _ (ht' i) _ (hE.trans (hT i)) _ (hD.trans (hT i)) _ (hr.trans (hT i)) o _ (Y.wood i.a i.b) rfl rfl).trans (hi i)
    have H' i:= ((S i).render _ (hx i) E (hE.trans (hT i)) D (hD.trans (hT i)) l (hl.trans (hT i)) u (hu.trans (hT i)) o).trans (hi i)
    exact ⟨hs.below fun i=>(le_add_of_nonneg_right (abs_nonneg _)).trans (H' i),hs.below fun i=> (le_add_of_nonneg_left (abs_nonneg _)).trans (H' i)⟩
end
end YM.FormalBulk08.Borough
