import YM.AllOrder.Burn.Icon
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Brim.Level
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Brim
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision Window Control
open Push.SectorMeasure.Oriented Scroll Vine Census Progress.StationaryScenes Progress.StationaryScenes.Green Hues Rotation
open Malachite Matter Shell Flux Poll Pond Silica Eider Metric Set Gaussian Tablet Quill Baffle Prism
open WardBin.Lies Push.PriceCompiler Foramen Gate
open Packets Art Gas Ursell Trees Multiple Letter OmitClusters Stained March Shield Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S}
variable {p j n m k : ℕ} {L : Side} {V : Config G c}
variable {d A α t C w M N v q r η W μ x b : ℝ} {Q : ConnectedActivityE6.Target G P} {o : ConnectedActivityE6.Target.Order G W} {R : Rep G f}
variable (H : Cash W x μ L Q o α T R)
open YM.AllOrder.Burn
/-! Variation of Release.chorus & Brim.pressings credited to given subset.
Supports & all directions.H true. Thus genuinely usable.C.Level.
-/
lemma chorusT (σ:ℝ) {a:Activities G f} (M:Set ℕ)(τ : ℕ → ℝ)
    {r:ℕ} {labels:ℕ→ RegularAddress c} {P B:BudgetPoint}{D:Record}{C:Libretto G n}{t E u x:ℝ}{Pt:Teller G}{q:Chi}{d:ℝ}
    (Z : ∀ i, Script G S (a.reg i).support (labels i).support r x) (hs : ∀ i, (labels i).site=S.ratio.parent (a.reg i).site)
    (hg : G.Simple) (hq : Release.Quotation C P.power r B.supportExponent t E) (h : Plays C D P B Pt T x) (hA : Release.accepts r B.supportExponent t S.patch.L) (hP : P.B=radiusB x) (hu : 0≤u)
    (hC : Lute.Plented C D P B S.patch.L r x u) (hh : ∀ i,(Z i).Played n u (D.ε*B.threshold)) (hE : a.RegularFamily B) (hτ : ∀ i,B.supBounds (a.reg i|>.site) (a.reg i|>.support) (a.E i) (τ i)) (h':∀ y:Site f, SumBudget (fun i=> if i∈M then 0 else wallet B a τ y i) σ) :
    ∃ v : ℕ→ℝ, (∀ i, i∉M→let f := (Z i).tuning u q d (a.E i) T; P.Regular (labels i).support f ∧ P.supBounds (labels i).site (labels i).support f (v i)) ∧ (∀ i,0≤v i) ∧ Footprint.Anchored (fun i => (labels i).site) v (fun i => coverNumber P.B (labels i).support) t (E/(S.patch.L.val:ℝ)*σ) := by
  let v i := τ i * Lute.returnFee C D P B S.patch.L (a.reg i).support r x u
  have hc i := (Z i).choirs (q:=q) (d:=d) hg h (Seed.family hE i) (hτ i) hu (hh i)
  have he i := hq.prices S D P B _ _ u x rfl rfl hA (Z i).fields hP (by rw [hP]; exact h.rehearsed.weft.cover) (by rw [h.rehearsed.temp_eq]; exact h.rehearsed.tensions.coarse) hu hC (τ i) (hτ i).1
  let p(i:ℕ):=if i∈M then 0 else v i; let f i:= B.mass (a.reg i|>.support) (if i∈M then 0 else τ i); have hp i:0≤ p i:= by unfold p; split; rfl; exact (hc i).2.1
  refine ⟨p,fun i hi=> (by unfold p; rw [if_neg hi]; exact hs i ▸ hc i), hp,fun y=>?_⟩
  simp_rw [hs]
  let a'(i:ℕ):=(a.reg i).site
  have hκ (y':Site _) : SumBudget (fun i=> if a' i=y' then f i else 0) σ:= by convert h' y' using 2 with i; simp only [wallet,f,a']; split_ifs <;> first | exact mul_zero _ | rfl
  refine Release.spread S.ratio _ _ _ (fun i => mul_nonneg (hp i) (Real.exp_pos _).le) hκ (by linarith only [hq.nonneg]) (fun i=>?_) y
  unfold p f; split
  next hh=> simp [BudgetPoint.mass]
  next hh=> exact (mul_comm ..).le.trans (he i)
-- Earn at chosen e when spun valuation. Need `Plays` from original.T.Batch not altered.
structure Homes (M:Set ℕ) (H : Cash W x μ L Q o α T R) (D : Record) (q' κ χ : Chi) (ε : ℝ) (B : BudgetPoint) (t c c' : ℝ) : Prop where
 principal : ∃ s : ℕ→ℝ, (∀ i, i∉M→ let f := announced H D q' κ ε i; B.Regular (plate H i).support f ∧ B.supBounds (plate H i).site (plate H i).support f (s i)) ∧ (∀ i,0 ≤ s i)∧
   Footprint.Anchored (fun i=> (plate H i).site) s (fun i=>coverNumber B.B (plate H i).support) t c
 remains : ∃ s : ℕ→ℝ, Footprint.Anchored (fun i=> (plate H i).site) s (fun i=> coverNumber B.B (plate H i).support) t c' ∧ (∀ i,0 ≤ s i)∧
   ∀ i, i∉M→ B.Regular (plate H i).support (glyph H D q' κ χ ε i) ∧ (coverNumber B.B (plate H i).support ≤ B.B → B.supBounds (plate H i).site (plate H i).support (glyph H D q' κ χ ε i) (s i))
section issuance
variable (G : Gauge) (hG : G.Simple) (P : Teller G) (L : Side) (D : Patch) (hD : D.Branches P.bind G) (p n : ℕ)
    (C : Libretto G n) (D' : Record) (hD' : D'.ε ≤ 1/4) (hn : 2≤n) (χ κ : Chi) (W : ℝ) (o : ConnectedActivityE6.Target.Order G W) (η : ℝ) (R₀ : ℕ) (he : 0 ≤ η)
include hG hD hD' hn he

lemma selectiveP : ∃ e : ℝ→ℝ, Rate G L (-(1/2)) e ∧ ∀ᶠ s in atTop,
    ∀ (c f : Side) (S : StepData c f) (T : Tube G S), S.patch=D → Works P L s S T →
      ∀ (R : Rep G f) (Q : ConnectedActivityE6.Target G P) (μ α:ℝ) (H:Cash W s μ L Q o α T R) (B:BudgetPoint),
        B.B=radiusB s→ B.power=p→ Plays C D' B R.p P T s → Q.halo+5 ≤ R₀ → ∀ C' : ℝ, Release.accepts R₀ R.p.supportExponent η L → Release.Quotation C p R₀ R.p.supportExponent η C' →
        Lute.Plented C D' B R.p L R₀ s (gStep R.beta)→ ∀ (j:ℕ), n≤ j → ∀ (A b d t Y B₀ r v q : ℝ) (k : ℕ), Captain H j Y d v t A b r B₀ q k χ → ∀ q ε, ∀ (M:Set ℕ) (Cx δ:ℝ), Candor R.p R.activities M Cx δ→ δ ≤ incomingE G L s→ Homes M H D' q κ χ ε B η (C'/L.val*δ) (|e s| *δ) := by
  obtain ⟨E,hE,hq⟩:= royaltyB G P L D hD n p C D' hn W o χ κ hD'
  let e x:= |E x| * expatriate L η R₀ /L.val
  refine ⟨e,(by unfold e; simp_rw [div_eq_mul_inv]; exact ((absolut hE).mul_right _).mul_right _),?_⟩
  filter_upwards [hq] with s hh c f S T hS hs R Q μ α H B ht hb hV hv C' hA hC hB j hJ A b d t Y B₀ r v q k N q' ε M Cx δ hR hδ
  have hf:=H.laws.intake; let K := S.patch.L; have hE:S.patch.L=L:= H.laws.data.funds.length_eq
  have h₀ : 0<gStep R.beta:= inv_pos.mpr (Real.sqrt_pos.mpr hf.positive); let σ:=scroll H D' κ hv
  obtain ⟨τ,hτ,hT⟩:= hR.sale
  obtain ⟨p₀,h,hκ,hP⟩:= chorusT δ M τ (q:=q') (d:=ε) (labels:=plate H) σ (fun _=>rfl) hG (hb.symm ▸ hC) hV (hE.symm ▸ hA) ht h₀.le
    (hE.symm ▸ hB) (fun i=> show (σ i).Played n (gStep R.beta) (D'.ε*R.p.threshold) from ⟨fun t=> guard_silent κ h₀ (mul_pos D'.guards R.p.threshold_pos)⟩) hf.cap.labels.regular hτ (fun i => (hT i).2)
  have he i : announced H D' q' κ ε i= _ := arithmetic H D' q' κ ε hv i
  have h₁ i := h i
  have h₂ i (hi:i∉M) : B.Regular (plate H i).support (announced H D' q' κ ε i) ∧ B.supBounds (plate H i).site (plate H i).support (announced H D' q' κ ε i) (p₀ i) := (he i).symm ▸ h₁ i hi -- edit
  let t₀ i:= if i∈M then 0 else τ i; have hΩ i:0≤ t₀ i:= by unfold t₀; split; rfl; exact (hτ i).1
  refine ⟨⟨p₀,h₂,hκ,by rwa [hE] at hP⟩, ⟨fun i=> t₀ i*|E s|, ?_,(fun i=>mul_nonneg (hΩ i) (abs_nonneg _)),?_⟩⟩
  · rw [abs_of_nonneg (show 0≤e s by unfold e expatriate; positivity)]
    exact landing H hv B hV ht (by assumption) hA hΩ _ (fun i=>(by convert! (hT i).2 using 2 with j; simp only [t₀,wallet]; split_ifs <;> first| exact mul_zero _| rfl)) |E s| (abs_nonneg _)
  intro i hi; simp only [show t₀ i= τ i from if_neg hi]; have hK:B.order≤j:= hV.rehearsed.test.le.trans hJ
  refine ⟨legal H D' q' κ χ ε hV i N hK (h₂ i hi).1, fun hx=>round H D' q' κ χ ε hV i N hK ht (h₂ i hi).1 (mul_nonneg (hτ i).1 (abs_nonneg _)) hx ?_⟩
  intro U hU z hz T' h' hα
  simp only [Function.comp_def, glyph]; simp_rw [lily]
  apply average H (κ:=κ) q' ε N hV i T' hU hG (hτ i) (E s)
  intro F Y
  have ht':= hT (R.activities.reg i).site; have hv : τ i ≤ incomingE G L s := by
    refine le_trans ?_ hδ; exact (R.p.loMass _ _ (hτ i).1).trans (by simpa [wallet,hi] using budget_single ht'.2 i)
  have hχ : (foyer H i F χ U Y).manifest := planted_valid (Greenbelt.prism T s χ o.K U F) _
  exact hh c f S T hS hs R Q μ α H F _ i rfl rfl rfl rfl hχ B ht hb hV (plate H i).support (Key (R.activities.reg i).support s F)
     (mapcase H i F) q' ε (τ i) _ (plate H i).anchor (ht ▸ hx) hU (grove H i Y F hU hV.rehearsed.temp_eq) (hτ i) hv z hz T' h' (hb ▸ hα) -- edit
end issuance
end YM.PhysicalNext.Repeat.Brim
