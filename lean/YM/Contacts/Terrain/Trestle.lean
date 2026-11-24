import YM.Contacts.Terrain.Height
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Brim.Level
/-! Adapted from Brim.Level & Release -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Heir
open Filter Function Set Lattice Wilson Pressure RG Tree Precision Next Next.SectorChange Rows Exterior Bloch
    Planned.AtomRegular MeasureTheory AnalyticBridge.LocalGaussian Push.AbsoluteSums Push.SectorMeasure
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {f c : Side} {S : StepData c f} {L : Side} {P B : BudgetPoint} {x u A t E τ : ℝ} {n p r : ℕ} {C : Libretto G n} {D : Record} {Pt : Teller G} {T : Tube G S}
    {q : Chi} {d : ℝ}
namespace Release

variable {C : Libretto G n}
theorem momentia {a : Activities G f} {labels : ℕ → RegularAddress c} (σ : ∀ i, Script G S (a.reg i).support (labels i).support r x) (hs : ∀ i, (labels i).site=S.ratio.parent (a.reg i).site)
    (hg : G.Simple) (hq : Quotation C P.power r B.supportExponent t E) (h : Plays C D P B Pt T x) (hA : accepts r B.supportExponent t S.patch.L) (hP : P.B=radiusB x) (hu : 0≤u)
    (hC : Lute.Plented C D P B S.patch.L r x u) (hh : ∀ i,(σ i).Played n u (D.ε*B.threshold)) (hE : a.RegularFamily B) (w Ω:ℕ→ℝ) (hω:∀ i,0≤Ω i) (hw:∀ i, B.supBounds (a.reg i).site (a.reg i).support (a.E i) (w i)) (hτ: ∀ u:Site f, SumBudget (fun i=> if (a.reg i).site=u then B.mass (a.reg i).support ((Ω*w) i) else 0) τ) :
    ∃ v : ℕ→ℝ, (∀ i, let f := (σ i).tuning u q d (a.E i) T; P.Regular (labels i).support f ∧ P.supBounds (labels i).site (labels i).support f (v i)) ∧
      Footprint.Anchored (fun i => (labels i).site) (Ω*v) (fun i => coverNumber P.B (labels i).support) t (E/(S.patch.L.val:ℝ)*τ) := by
  let v i := w i * Lute.returnFee C D P B S.patch.L (a.reg i).support r x u
  have hc i := (σ i).choirs (q:=q) (d:=d) hg h (Seed.family hE i) (hw i) hu (hh i)
  have he i := hq.prices S D P B _ _ u x rfl rfl hA (σ i).fields hP (by rw [hP]; exact h.rehearsed.weft.cover) (by rw [h.rehearsed.temp_eq]; exact h.rehearsed.tensions.coarse) hu hC ((Ω*w) i) (mul_nonneg (hω _) (hw i).1)
  refine ⟨v,fun i => hs i ▸ hc i,fun y => ?_⟩
  simp_rw [hs]
  exact spread S.ratio _ _ _ (fun i => mul_nonneg (mul_nonneg (hω _) (hc i).2.1) (Real.exp_pos _).le) hτ (by linarith only [hq.nonneg]) (fun i => Eq.trans_le (b:=_) (c:=_) (a:=((Ω*v) i)*Real.exp (t*coverNumber P.B (labels i).support)) (by change Ω i*v i*_= Real.exp _ *((Ω*w) i * _); unfold v; rw [Pi.mul_apply]; ring) (he i)) y
end Release
end YM.PhysicalNext.JointLoad.Heir


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

section issuance
variable (G : Gauge) (hG : G.Simple) (P : Teller G) (L : Side) (D : Patch) (hD : D.Branches P.bind G) (p n : ℕ)
    (C : Libretto G n) (D' : Record) (hD' : D'.ε ≤ 1/4) (hn : 2≤n) (χ κ : Chi) (W : ℝ) (o : ConnectedActivityE6.Target.Order G W) (η : ℝ) (R₀ : ℕ) (he : 0 ≤ η)
include hG hD hD' hn he

lemma apogee : ∃ e : ℝ→ℝ, Rate G L (-(1/2)) e ∧ ∀ᶠ s in atTop,
    ∀ (c f : Side) (S : StepData c f) (T : Tube G S), S.patch=D → Works P L s S T →
      ∀ (R : Rep G f) (Q : ConnectedActivityE6.Target G P) (μ α:ℝ) (H:Cash W s μ L Q o α T R) (B:BudgetPoint),
        B.B=radiusB s→ B.power=p→ Plays C D' B R.p P T s → Q.halo+5 ≤ R₀ → ∀ C' : ℝ, Release.accepts R₀ R.p.supportExponent η L → Release.Quotation C p R₀ R.p.supportExponent η C' →
        Lute.Plented C D' B R.p L R₀ s (gStep R.beta)→ ∀ (j:ℕ), n≤ j → ∀ (A b d t Y B₀ r v q : ℝ) (k : ℕ), Captain H j Y d v t A b r B₀ q k χ → ∀ (q':Chi)(ε:ℝ)(Ω τ:ℕ→ℝ)(u:ℝ), (∀ i,0≤Ω i) → (∀ i,R.p.supBounds (R.activities.reg i).site (R.activities.reg i).support (R.activities.E i) (τ i)∧ τ i≤ incomingE G L s) → (∀ u':Site f, SumBudget (fun i=>if (R.activities.reg i).site=u' then R.p.mass (R.activities.reg i).support ((Ω*τ) i) else 0) u) →
        ∃ (b₁ b₂:ℕ→ℝ), (∀ i, B.Regular (plate H i).support (announced H D' q' κ ε i) ∧ B.supBounds (plate H i).site (plate H i).support (announced H D' q' κ ε i) (b₁ i)) ∧ Footprint.Anchored (fun i => (plate H i).site) (Ω*b₁) (fun i => coverNumber B.B (plate H i).support) η (C'/(L.val:ℝ)*u) ∧ Footprint.Anchored (fun i=> (plate H i).site) (Ω*b₂) (fun i=>coverNumber B.B (plate H i).support) η (|e s| *u) ∧
        ∀ i, 0≤b₂ i ∧ B.Regular (plate H i).support (glyph H D' q' κ χ ε i) ∧ (coverNumber B.B (plate H i).support ≤ B.B → B.supBounds (plate H i).site (plate H i).support (glyph H D' q' κ χ ε i) (b₂ i)) := by
  obtain ⟨E,hE,hq⟩:= royaltyB G P L D hD n p C D' hn W o χ κ hD'
  let e x:= |E x| * expatriate L η R₀ /L.val
  refine ⟨e,(by unfold e; simp_rw [div_eq_mul_inv]; exact ((absolut hE).mul_right _).mul_right _),?_⟩
  filter_upwards [hq] with s hh c f S T hS hs R Q μ α H B ht hb hV hv C' hA hC hB j hJ A b d t Y B₀ r v q k N q' ε Ω τ u hΩ hτ' hT
  have hτ i:= (hτ' i).1
  have hf:=H.laws.intake; let K := S.patch.L; have hE:S.patch.L=L:= H.laws.data.funds.length_eq
  have h₀ : 0<gStep R.beta:= inv_pos.mpr (Real.sqrt_pos.mpr hf.positive); let σ:=scroll H D' κ hv
  obtain ⟨p₀,h,hP⟩:= Release.momentia (q:=q') (d:=ε) (labels:=plate H) σ (fun _=>rfl) hG (hb.symm ▸ hC) hV (hE.symm ▸ hA) ht h₀.le
    (hE.symm ▸ hB) (fun i=> show (σ i).Played n (gStep R.beta) (D'.ε*R.p.threshold) from ⟨fun t=> guard_silent κ h₀ (mul_pos D'.guards R.p.threshold_pos)⟩) hf.cap.labels.regular τ Ω hΩ hτ hT
  have he i : announced H D' q' κ ε i= _ := arithmetic H D' q' κ ε hv i
  have h₁ i := h i
  have h₂ i : B.Regular (plate H i).support (announced H D' q' κ ε i) ∧ B.supBounds (plate H i).site (plate H i).support (announced H D' q' κ ε i) (p₀ i) := (he i).symm ▸ h₁ i -- edit
  refine ⟨p₀,fun i=> τ i*|E s|,h₂,by rwa [hE] at hP, ?_,?_⟩
  · rw [abs_of_nonneg (show 0≤e s by unfold e expatriate; positivity)]
    convert landing H hv B hV ht (by assumption) hA (fun i=> show 0≤(Ω*τ) i from mul_nonneg (hΩ i) (hτ i).1) _ hT |E s| (abs_nonneg _) using 1; ext i; exact (mul_assoc ..).symm
  intro i; have hK:B.order≤j:= hV.rehearsed.test.le.trans hJ
  refine ⟨mul_nonneg (hτ i).1 (abs_nonneg _),legal H D' q' κ χ ε hV i N hK (h₂ i).1, fun hx=>round H D' q' κ χ ε hV i N hK ht (h₂ i).1 (mul_nonneg (hτ i).1 (abs_nonneg _)) hx ?_⟩
  intro U hU z hz T' h' hα
  simp only [Function.comp_def, glyph]; simp_rw [lily]
  apply average H (κ:=κ) q' ε N hV i T' hU hG (hτ i) (E s)
  intro F Y
  have hv:= (hτ' i).2
  have hχ : (foyer H i F χ U Y).manifest := planted_valid (Greenbelt.prism T s χ o.K U F) _
  exact hh c f S T hS hs R Q μ α H F _ i rfl rfl rfl rfl hχ B ht hb hV (plate H i).support (Key (R.activities.reg i).support s F)
     (mapcase H i F) q' ε (τ i) _ (plate H i).anchor (ht ▸ hx) hU (grove H i Y F hU hV.rehearsed.temp_eq) (hτ i) hv z hz T' h' (hb ▸ hα) -- edit
end issuance
end YM.PhysicalNext.Repeat.Brim
