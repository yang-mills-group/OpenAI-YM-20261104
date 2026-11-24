import YM.LocalLTE.Tier.Fly
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Brim.Level
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Brim.Lode

/-! # First-order inheritance at real calendar S levels. Price after *subtracting* V9.

At exact INPUT α legacy-occurrence. Supplies sharp early cost (principal
 portion at U_E/L × intake; need turned L choice) for surviving singles.
 Full P+3 must still fit later transitions. Does not redraw Forest or μ.
 Same θ average on Auth. Consume alongside Cohorts. -/
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

structure Hauses (F:ℕ→ℝ) (H : Cash W x μ L Q o α T R) (D : Record) (q' κ χ : Chi) (ε : ℝ) (B : BudgetPoint) (t c c' : ℝ) : Prop where
  principal : ∃ s : ℕ→ℝ, (∀ i, let f := announced H D q' κ ε i; B.Regular (plate H i).support f ∧ B.supBounds (plate H i).site (plate H i).support f (s i)) ∧
    Footprint.Anchored (fun i=> (plate H i).site) (fun i=> F i*s i) (fun i=>coverNumber B.B (plate H i).support) t c
  remains : ∃ s : ℕ→ℝ, Footprint.Anchored (fun i=> (plate H i).site) (fun i=> F i*s i) (fun i=> coverNumber B.B (plate H i).support) t c' ∧
    ∀ i, B.Regular (plate H i).support (glyph H D q' κ χ ε i) ∧
      (coverNumber B.B (plate H i).support ≤ B.B → B.supBounds (plate H i).site (plate H i).support (glyph H D q' κ χ ε i) (s i))

section issuance
variable (G : Gauge) (hG : G.Simple) (P : Teller G) (L : Side) (D : Patch) (hD : D.Branches P.bind G) (p n : ℕ)
    (C : Libretto G n) (D' : Record) (hD' : D'.ε ≤ 1/4) (hn : 2≤n) (χ κ : Chi) (W : ℝ) (o : ConnectedActivityE6.Target.Order G W) (η : ℝ) (R₀ : ℕ) (he : 0 ≤ η)
include hG hD hD' hn he

lemma pressTier : ∃ e : ℝ→ℝ, Rate G L (-(1/2)) e ∧ ∀ᶠ s in atTop,
    ∀ (c f : Side) (S : StepData c f) (T : Tube G S), S.patch=D → Works P L s S T →
      ∀ (R : Rep G f) (Q : ConnectedActivityE6.Target G P) (μ α:ℝ) (H:Cash W s μ L Q o α T R) (B:BudgetPoint),
        B.B=radiusB s→ B.power=p→ Plays C D' B R.p P T s → Q.halo+5 ≤ R₀ → ∀ C' : ℝ, Release.accepts R₀ R.p.supportExponent η L → Release.Quotation C p R₀ R.p.supportExponent η C' →
        Lute.Plented C D' B R.p L R₀ s (gStep R.beta)→ ∀ (j:ℕ), n≤ j → ∀ (A b d t Y B₀ r v q : ℝ) (k : ℕ), Captain H j Y d v t A b r B₀ q k χ → ∀ q ε ξ F', Raw.Pumps R F' ξ → Hauses F' H D' q κ χ ε B η (C'/L.val*ξ) (|e s| *ξ) := by
  obtain ⟨E,hE,hq⟩:= royaltyB G P L D hD n p C D' hn W o χ κ hD'
  let e x:= |E x| * expatriate L η R₀ /L.val
  refine ⟨e,(by unfold e; simp_rw [div_eq_mul_inv]; exact ((absolut hE).mul_right _).mul_right _),?_⟩
  filter_upwards [hq] with s hh c f S T hS hs R Q μ α H B ht hb hV hv C' hA hC hB j hJ A b d t Y B₀ r v q k N q' ε ξ F' hp
  have hf:=H.laws.intake; let K := S.patch.L; have hE:S.patch.L=L:= H.laws.data.funds.length_eq
  have h₀ : 0<gStep R.beta:= inv_pos.mpr (Real.sqrt_pos.mpr hf.positive); let σ:=scroll H D' κ hv
  obtain ⟨u,hs0,hy⟩:= hf.cap.labels.boundE
  obtain ⟨hf0,w,hs1,hE'⟩:= hp
  let τ i:= min (u i) (w i); have hv' i:τ i ≤w i:= min_le_right ..; have hv0 i:0≤ F' i:= zero_le_one.trans (hf0 _)
  have hτ i:R.p.supBounds (R.activities.reg i).site (R.activities.reg i).support (R.activities.E i) (τ i):= by
    by_cases h:u i≤w i; · unfold τ; rw [min_eq_left h]; exact hs0 _
    unfold τ; rw [min_eq_right (le_of_not_ge h)]; exact hs1 _
  have hζ y:= budget_mono (g:=fun i => if (R.activities.reg i).site=y then R.p.mass (R.activities.reg i).support (F' i*τ i) else 0) (hE' y) (fun i=>by
    split; next => unfold BudgetPoint.mass; (exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (hv0 i) (hτ i).1))
    exact le_rfl) (fun i=>by
    split; next => unfold BudgetPoint.mass; gcongr; exact hv0 i; exact hv' i
    exact le_rfl)
  let p₀ i:= τ i * Lute.returnFee C D' B R.p S.patch.L (R.activities.reg i).support R₀ s (gStep R.beta)
  have h i := (σ i).choirs (q:=q') (d:=ε) hG hV (Seed.family hf.cap.labels.regular i) (hτ i) h₀.le
    (show (σ i).Played n (gStep R.beta) (D'.ε*R.p.threshold) from ⟨fun t=> guard_silent κ h₀ (mul_pos D'.guards R.p.threshold_pos)⟩)
  have hQ i:= hC.prices S D' B R.p _ _ (gStep R.beta) s hb rfl (hE.symm ▸ hA) (σ i).fields ht (by rw [ht]; exact hV.rehearsed.weft.cover) (by rw [hV.rehearsed.temp_eq]; exact hV.rehearsed.tensions.coarse) h₀.le (hE.symm ▸ hB) (F' i*τ i) (mul_nonneg (hv0 i) (hτ i).1)
  have he i : announced H D' q' κ ε i= _ := arithmetic H D' q' κ ε hv i
  have h₁ i : B.Regular (plate H i).support (announced H D' q' κ ε i) ∧ B.supBounds (plate H i).site (plate H i).support (announced H D' q' κ ε i) (p₀ i) := by rw [he]; unfold p₀; exact h i
  refine ⟨⟨p₀,h₁,fun y=>?_⟩, ⟨fun i=>τ i*|E s|, ?_,?_⟩⟩
  · rw [show L.val=S.patch.L.val by rw [hE]]; apply Release.spread S.ratio _ _ (fun i=> F' i*p₀ i * Real.exp (η*coverNumber B.B (plate H i).support)) (fun i=> mul_nonneg (mul_nonneg (hv0 i) (h₁ i).2.1) (Real.exp_pos _).le) hζ (zero_le_one.trans hC.nonneg) (fun i=>?_) y
    rw [mul_comm]; unfold p₀; rw [← mul_assoc (F' i)]; exact hQ _
  · rw [abs_of_nonneg (show 0≤e s by unfold e expatriate; positivity)]
    have hp:= landing H hv B hV ht (by assumption) hA (τ:=fun i=> F' i*τ i) (fun i=> mul_nonneg (hv0 i) (hτ i).1) _ hζ |E s| (abs_nonneg _)
    simp_rw [mul_assoc (F' _)] at hp; exact hp
  intro i; have hK:B.order≤j:= hV.rehearsed.test.le.trans hJ
  refine ⟨legal H D' q' κ χ ε hV i N hK (h₁ i).1, fun hx=>round H D' q' κ χ ε hV i N hK ht (h₁ i).1 (mul_nonneg (hτ i).1 (abs_nonneg _)) hx ?_⟩
  intro U hU z hz T' h' hα
  simp only [Function.comp_def, glyph]; simp_rw [lily]
  apply average H (κ:=κ) q' ε N hV i T' hU hG (hτ i) (E s)
  intro F Y
  have ht':= hy (R.activities.reg i).site; have hv : τ i ≤ incomingE G L s := by
    rw [← hE]; apply (le_trans (min_le_left (u i) _)); exact (R.p.loMass _ (u i) (hs0 i).1).trans (by simpa using budget_single ht' i)
  have hχ : (foyer H i F χ U Y).manifest := planted_valid (Greenbelt.prism T s χ o.K U F) _
  exact hh c f S T hS hs R Q μ α H F _ i rfl rfl rfl rfl hχ B ht hb hV (plate H i).support (Key (R.activities.reg i).support s F)
     (mapcase H i F) q' ε (τ i) _ (plate H i).anchor (ht ▸ hx) hU (grove H i Y F hU hV.rehearsed.temp_eq) (hτ i) hv z hz T' h' (hb ▸ hα) -- edit
end issuance
end YM.PhysicalNext.Repeat.Brim
