import YM.RG01Estimate.FateRates

/-! Sharpened Brim.Houses on an arbitrary inherited subpopulation. The Lipschitz
scaling here is per actual derivative-budget input, not scaling after differentiating
a profile whose active domain moved. Works for the genuine single-E exception
(`Brim.icon`); not used on marks or winding stencils. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Single
open Function Filter Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push Push.SectorMeasure Push.AbsoluteSums Exterior
open PhysicalNext PhysicalNext.Repeat Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision Window Control
open Push.SectorMeasure.Oriented Scroll Vine Census Progress.StationaryScenes Progress.StationaryScenes.Green Hues Rotation
open Malachite Matter Shell Flux Poll Pond Silica Eider Metric Set Gaussian Tablet Quill Baffle Prism
open WardBin.Lies Push.PriceCompiler Foramen Gate
open Packets Art Gas Ursell Trees Multiple Letter OmitClusters Stained March Shield Greenbelt Brim Release
open AnalyticBridge VerifiedReset Collection
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {p j r n m : ℕ} {L : Side}
    {x W μ α : ℝ} {D' : Record} {Q : ConnectedActivityE6.Target G P} {o : ConnectedActivityE6.Target.Order G W} {R : RG.Rep G f}

-- variant of pressings: per-price, for an arbitrary distinguished e subfamily
-- only gives supBounds on paid sizes ≤ B.B; others are charged already by Shape tails
structure Pays (H : Cash W x μ L Q o α T R) (K : BudgetPoint) (E : Set ℕ) (χ : Chi) (η u : ℝ) : Prop where
  envelope : ∃ t : ℕ→ℝ,
    Footprint.Anchored (fun i=> (Brim.plate H i).site) t (fun i=> coverNumber K.B (Brim.plate H i).support) η u ∧
      ∀ i∈E, coverNumber K.B (Brim.plate H i).support ≤ K.B →
        K.supBounds (Brim.plate H i).site (Brim.plate H i).support (fun V=> March.stream H χ V (icon H i)) (t i)

-- work at any announced principal formula in bought regime
section issuance
variable (G : Gauge) (hG : G.Simple) (P : Teller G) (L : Side) (D : Patch) (hD : D.Branches P.bind G) (p n : ℕ)
    (C : Libretto G n) (D' : Record) (hD' : D'.ε ≤ 1/4) (hn : 2≤n) (χ κ : Chi) (W : ℝ) (o : ConnectedActivityE6.Target.Order G W) (η : ℝ) (R₀ : ℕ) (he : 0 ≤ η)

-- formulation matching Activation: arbitrary subset, contraction coefficient independent of summability horizon.
def Gate (B : ℝ) (x : ℝ) :=
    ∀ (c f : Side) (S : StepData c f) (T : Tube G S), Works P L x S T →
      ∀ (R : Rep G f) (Q : ConnectedActivityE6.Target G P) (μ α:ℝ) (H:Cash W x μ L Q o α T R) (K:BudgetPoint),
        K.B=radiusB x→ K.power=p→ Plays C D' K R.p P T x → Q.halo+5 ≤ R₀ → ∀ C' : ℝ, Release.accepts R₀ R.p.supportExponent η L →
        Release.Quotation C p R₀ R.p.supportExponent η C' → Lute.Plented C D' K R.p L R₀ x (gStep R.beta)→
         ∀ (j:ℕ), n≤ j → ∀ (A b d t Y B₀ r v q : ℝ) (k : ℕ), Captain H j Y d v t A b r B₀ q k χ →
        ∀ τ : ℝ, τ ≤ incomingE G L x → ∀ E : Set ℕ, Inherit.Debits R E τ → Pays H K E χ η ((C'/L.val+B)*τ)

include hG hD hD' hn κ he
lemma bystage (hL : D.L=L) (hp : D.J=P.j) : ∃ t : ℝ→ℝ, Rate G L (-(1/2)) t ∧ ∀ᶠ s in atTop,
    Single.Gate G P L p n C D' χ W o η R₀ |t s| s := by
  obtain ⟨z,hT,hq⟩:= Brim.royaltyB G P L D hD n p C D' hn W o χ κ hD'
  let e x:= |z x| * expatriate L η R₀ /L.val
  refine ⟨e,(by unfold e; simp_rw [div_eq_mul_inv]; exact ((absolut hT).mul_right _).mul_right _),?_⟩
  filter_upwards [hq] with s hh c f S T hS R Q μ α H B ht hb hV hv C' hA hC hB j hJ A b d t Y B₀ r v q k N τ hx X hX
  have hf:=H.laws.intake; let K := S.patch.L
  have hE:S.patch.L=L:= H.laws.data.funds.length_eq
  have h₀ : 0<gStep R.beta:= inv_pos.mpr (Real.sqrt_pos.mpr hf.positive)
  let σ:=scroll H D' κ hv
  let a:=Inherit.selected R X
  obtain ⟨p₀,h,hP⟩:= Release.chorus (a:=Inherit.selected R X) (τ:=τ) (q:=κ) (d:=0) (labels:=plate H) σ (fun _=>rfl) hG (hb.symm ▸ hC) hV
    (hE.symm ▸ hA) ht h₀.le (hE.symm ▸ hB) (fun i=> show (σ i).Played n (gStep R.beta) (D'.ε*R.p.threshold) from
      ⟨fun t=> guard_silent κ h₀ (mul_pos D'.guards R.p.threshold_pos)⟩) (Inherit.flagged hf X) hX
  obtain ⟨τ',hτ,hT⟩:= hX
  have hy i (hi:i∈X) : a.E i=R.activities.E i:= if_pos hi
  let f i:=τ' i*|z s|
  have ht':Footprint.Anchored (fun i=> (plate H i).site) f (fun i=> coverNumber B.B (plate H i).support) η (|e s| * τ):= by
    rw [abs_of_nonneg (show 0≤ e s by unfold e expatriate; positivity)]
    exact landing H hv B hV ht he hA (fun i=> (hτ i).1) _ hT |z s| (abs_nonneg _)
  refine ⟨fun i=>f i+p₀ i,fun i=>?_,fun i hi hy'=> ?_⟩
  · have hg := budget_plus (ht' i) (hP i)
    rw [hE] at hg
    convert hg using 2 <;> first | (rename_i i; dsimp only; split <;> ring) | ring
  have hz : R.activities.E i=a.E i:= (hy i hi).symm
  have hLog := arithmetic H D' κ κ 0 hv i
  have hxV: R.p.supBounds (R.activities.reg i).site (R.activities.reg i).support (R.activities.E i) (τ' i) := by
    change R.p.supBounds (a.reg i).site (a.reg i).support (R.activities.E i) (τ' i)
    rw [hz]; exact hτ i
  let F:= announced H D' κ κ 0 i
  let G':= glyph H D' κ κ χ 0 i
  have h₂ : B.Regular (plate H i).support F ∧ B.supBounds (plate H i).site (plate H i).support F (p₀ i) := by
    have hx : F=(σ i).tuning (gStep R.beta) κ 0 (a.E i) T:= by rw [hy _ hi]; exact hLog
    rw [hx]; exact h i
  have hK:B.order≤j:= hV.rehearsed.test.le.trans hJ
  have hG' : B.supBounds (plate H i).site (plate H i).support G' (f i):= by
    apply round H D' κ κ χ 0 hV i N hK ht h₂.1 (mul_nonneg hxV.1 (abs_nonneg _)) hy'
    intro U hU j hj T' h' hα
    simp only [Function.comp_def, glyph]; simp_rw [lily]
    apply average H (κ:=κ) κ 0 N hV i T' hU hG hxV (z s)
    intro F Y
    have ht':= hT (R.activities.reg i).site
    have hv : τ' i ≤ incomingE G L s := by
      have hu := budget_single ht' i
      simp only [Inherit.selected,↓reduceIte] at hu
      exact (R.p.loMass _ _ hxV.1).trans (hu.trans hx)
    have hχ : (foyer H i F χ U Y).manifest := planted_valid (Greenbelt.prism T s χ o.K U F) _
    exact hh c _ S T (hS.patch hL hp) hS R Q μ α H F _ i rfl rfl rfl rfl hχ B ht hb hV (plate H i).support (Key (R.activities.reg i).support s F)
      (mapcase H i F) κ 0 (τ' i) _ (plate H i).anchor (ht ▸ hy') hU (grove H i Y F hU hV.rehearsed.temp_eq) hxV hv j hj T' h' (hb ▸ hα)
  rw [show (fun V=> March.stream H χ V (icon H i))=G'-F from ?_]
  · exact CouplingShape.sup_sub (legal H D' κ κ χ 0 hV i N hK h₂.1) h₂.1 hG' h₂.2
  ext; simp [G',F,glyph]
end issuance

-- stage predicate purchase at any L after pricing spectrum
end YM.RG01Estimate.Single
