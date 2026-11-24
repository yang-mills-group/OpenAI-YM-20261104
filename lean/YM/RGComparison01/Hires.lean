import YM.RGComparison01.Tithe
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Brim.Level

/-! # Essential sharp step loss C_J/L for single rough E entries
 in the qev inherited-e test. Restrict the principal Singlets with exact
 sites. Not allocating the contribution of all incoming E to estimate e.
 Extend `pressings`. -/
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

structure Hired (H : Cash W x μ L Q o α T R) (Dg : ℕ → Prop) (D : Record) (q' κ χ : Chi) (ε : ℝ) (B : BudgetPoint) (t c c' : ℝ) : Prop where
  principal : ∃ s : ℕ→ℝ, (∀ i,Dg i → let f := announced H D q' κ ε i; B.Regular (plate H i).support f ∧ B.supBounds (plate H i).site (plate H i).support f (s i)) ∧
    Footprint.Anchored (fun i=> (plate H i).site) s (fun i=>coverNumber B.B (plate H i).support) t c
  remains : ∃ s : ℕ→ℝ, Footprint.Anchored (fun i=> (plate H i).site) s (fun i=> coverNumber B.B (plate H i).support) t c' ∧
    ∀ i,Dg i → B.Regular (plate H i).support (glyph H D q' κ χ ε i) ∧
      (coverNumber B.B (plate H i).support ≤ B.B → B.supBounds (plate H i).site (plate H i).support (glyph H D q' κ χ ε i) (s i))

section issuance
variable (G : Gauge) (hG : G.Simple) (P : Teller G) (L : Side) (D : Patch) (hD : D.Branches P.bind G) (p n : ℕ)
    (C : Libretto G n) (D' : Record) (hD' : D'.ε ≤ 1/4) (hn : 2≤n) (χ κ : Chi) (W : ℝ) (o : ConnectedActivityE6.Target.Order G W) (η : ℝ) (R₀ : ℕ) (he : 0 ≤ η)
include hG hD hD' hn he

open RGComparison01.Tithe
lemma hired_policy : ∃ e : ℝ→ℝ, Rate G L (-(1/2)) e ∧ ∀ᶠ s in atTop,
    ∀ (c f : Side) (S : StepData c f) (T : Tube G S), S.patch=D → Works P L s S T →
      ∀ (R : Rep G f) (Q : ConnectedActivityE6.Target G P) (μ α:ℝ) (H:Cash W s μ L Q o α T R) (B:BudgetPoint),
        B.B=radiusB s→ B.power=p→ Plays C D' B R.p P T s → Q.halo+5 ≤ R₀ → ∀ C' : ℝ, Release.accepts R₀ R.p.supportExponent η L → Release.Quotation C p R₀ R.p.supportExponent η C' →
        Lute.Plented C D' B R.p L R₀ s (gStep R.beta)→ ∀ (j:ℕ), n≤ j → ∀ (A b d t Y B₀ r v q : ℝ) (k : ℕ), Captain H j Y d v t A b r B₀ q k χ → ∀ (Dg : ℕ → Prop) (w : ℝ), (portion R.activities Dg).EBound R.p w → w ≤ incomingE G L s → ∀ q ε, Hired H Dg D' q κ χ ε B η (C'/L.val*w) (|e s| *w) := by
  obtain ⟨E,hE,hq⟩:= royaltyB G P L D hD n p C D' hn W o χ κ hD'
  let e x:= |E x| * expatriate L η R₀ /L.val
  refine ⟨e,(by unfold e; simp_rw [div_eq_mul_inv]; exact ((absolut hE).mul_right _).mul_right _),?_⟩
  filter_upwards [hq] with s hh c f S T hS hs R Q μ α H B ht hb hV hv C' hA hC hB j hJ A b d t Y B₀ r v q k N Z w₀ hw₀ hu₀ q' ε
  have hf:=H.laws.intake; let K := S.patch.L; have hE:S.patch.L=L:= H.laws.data.funds.length_eq
  have h₀ : 0<gStep R.beta:= inv_pos.mpr (Real.sqrt_pos.mpr hf.positive); let σ:=scroll H D' κ hv
  obtain ⟨p₀,h,hP⟩:= Release.chorus (a:=portion R.activities Z) (q:=q') (d:=ε) (labels:=plate H) σ (fun _=>rfl) hG (hb.symm ▸ hC) hV (hE.symm ▸ hA) ht h₀.le
    (hE.symm ▸ hB) (fun i=> show (σ i).Played n (gStep R.beta) (D'.ε*R.p.threshold) from ⟨fun t=> guard_silent κ h₀ (mul_pos D'.guards R.p.threshold_pos)⟩) (portion_regular R.activities R.p hf.cap.labels.regular Z) hw₀
  have he i : announced H D' q' κ ε i= _ := arithmetic H D' q' κ ε hv i
  have h₂ i (hi:Z i) : B.Regular (plate H i).support (announced H D' q' κ ε i) ∧ B.supBounds (plate H i).site (plate H i).support (announced H D' q' κ ε i) (p₀ i) := by rw [he]; simpa only [portion,if_pos hi] using h i
  obtain ⟨τ,hτ,hT⟩:= hw₀
  refine ⟨⟨p₀,h₂,by rwa [hE] at hP⟩, ⟨fun i=> τ i*|E s|, ?_,?_⟩⟩
  · rw [abs_of_nonneg (show 0≤e s by unfold e expatriate; positivity)]
    exact landing H hv B hV ht (by assumption) hA (fun i=> (hτ i).1) _ hT |E s| (abs_nonneg _)
  intro i hi
  have hu : R.p.supBounds (R.activities.reg i).site (R.activities.reg i).support (R.activities.E i) (τ i):= by simpa only [portion,if_pos hi] using hτ i
  have hK:B.order≤j:= hV.rehearsed.test.le.trans hJ
  refine ⟨legal H D' q' κ χ ε hV i N hK (h₂ i hi).1, fun hx=>round H D' q' κ χ ε hV i N hK ht (h₂ i hi).1 (mul_nonneg (hτ i).1 (abs_nonneg _)) hx ?_⟩
  intro U hU z hz T' h' hα
  simp only [Function.comp_def, glyph]; simp_rw [lily]
  apply average H (κ:=κ) q' ε N hV i T' hU hG hu (E s)
  intro F Y
  have ht':= hT (R.activities.reg i).site; have hv : τ i ≤ incomingE G L s := by
    exact ((R.p.loMass _ _ (hτ i).1).trans (by simpa only [portion, ↓reduceIte] using budget_single ht' i)).trans hu₀
  have hχ : (foyer H i F χ U Y).manifest := planted_valid (Greenbelt.prism T s χ o.K U F) _
  exact hh c f S T hS hs R Q μ α H F _ i rfl rfl rfl rfl hχ B ht hb hV (plate H i).support (Key (R.activities.reg i).support s F)
     (mapcase H i F) q' ε (τ i) _ (plate H i).anchor (ht ▸ hx) hU (grove H i Y F hU hV.rehearsed.temp_eq) hu hv z hz T' h' (hb ▸ hα)
end issuance
end YM.PhysicalNext.Repeat.Brim
