import YM.Integration.QLocalInheritedGlyphRate

/-! The physical singleton correction acts on the actual fine activity bill.
    Both the prequoted principal and the power-saving remainder use that bill. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalInheritedRelativeGlyph
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Brim
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube
open Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian
open JointLoad JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6
open ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows ConnectedActivityE6.Mask
open ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision Window Control
open Push.SectorMeasure.Oriented Scroll Vine Census Progress.StationaryScenes Progress.StationaryScenes.Green
open Hues Rotation Malachite Matter Shell Flux Poll Pond Silica Eider Metric Set Gaussian Tablet Quill Baffle Prism
open WardBin.Lies Push.PriceCompiler Foramen Gate
open Packets Art Gas Ursell Trees Multiple Letter OmitClusters Stained March Shield Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

private theorem tighten {G : Gauge} {n : Side} (R : Rep G n) {b c : ℝ}
    (paid : R.activities.EBound R.p b) (old : R.activities.EBound R.p c) :
    ∃ τ : ℕ → ℝ,
      (∀ i, R.p.supBounds (R.activities.reg i).site (R.activities.reg i).support (R.activities.E i) (τ i)) ∧
      (∀ x : Site n, SumBudget (fun i => if (R.activities.reg i).site=x then
        R.p.mass (R.activities.reg i).support (τ i) else 0) b) ∧ ∀ i, τ i ≤ c := by
  obtain ⟨u,hu,ub⟩ := paid
  obtain ⟨v,hv,vb⟩ := old
  refine ⟨fun i => min (u i) (v i),fun i => ⟨le_min (hu i).1 (hv i).1,
    fun U hU d hl hh => le_min ((hu i).2 U hU d hl hh) ((hv i).2 U hU d hl hh)⟩,?_,?_⟩
  · intro x
    apply budget_mono (ub x)
    · intro i
      split
      · exact mul_nonneg (Real.exp_nonneg _) (le_min (hu i).1 (hv i).1)
      · exact le_rfl
    · intro i
      split
      · exact mul_le_mul_of_nonneg_left (min_le_left _ _) (Real.exp_nonneg _)
      · exact le_rfl
  · intro i
    exact (min_le_right _ _).trans ((R.p.loMass _ _ (hv i).1).trans
      (by simpa using budget_single (vb (R.activities.reg i).site) i))

theorem issue (G : Gauge) (hG : G.Simple) (P : Teller G) (L : Side)
    (D : Patch) (hD : D.Branches P.bind G) (p n : ℕ) (C : Libretto G n) (M : Heir.Record)
    (hM : M.ε ≤ 1/4) (hn : 2 ≤ n) (χ κ : Chi) (W : ℝ) (o : Target.Order G W)
    (t : ℝ) (r : ℕ) (ht : 0 ≤ t) (γ : ℝ) (hγ : -(1/2 : ℝ) < γ) :
    ∀ᶠ x : ℝ in atTop, ∀ (c f : Side) (S : StepData c f) (T : Tube G S),
      S.patch = D → Works P L x S T → ∀ (R : Rep G f) (Q : Target G P) (μ α : ℝ)
      (H : Cash W x μ L Q o α T R) (B : BudgetPoint), B.B = radiusB x → B.power = p →
      Plays C M B R.p P T x → Q.halo+5 ≤ r → ∀ fee : ℝ,
      Release.accepts r R.p.supportExponent t L → Release.Quotation C p r R.p.supportExponent t fee →
      Lute.Plented C M B R.p L r x (gStep R.beta) → ∀ j : ℕ, n ≤ j →
      ∀ (A b d s Y B₀ r' v q : ℝ) (k : ℕ), Captain H j Y d v s A b r' B₀ q k χ →
      ∀ q' ε (incoming : ℝ), R.activities.EBound R.p incoming →
        Houses H M q' κ χ ε B t (fee/L.val*incoming) (betaF G x L ^ γ * incoming) := by
  obtain ⟨E,hE,estimate⟩ := royaltyB G P L D hD n p C M hn W o χ κ hM
  let cost x := |E x| * expatriate L t r / L.val
  have rate : Rate G L (-(1/2)) cost := by
    unfold cost
    simp_rw [div_eq_mul_inv]
    exact ((absolut hE).mul_right _).mul_right _
  filter_upwards [estimate,rate γ hγ] with x hx small c f S T hS hs R Q μ α H B hr hp
    hplays hhalo fee hA hQ hC j hj A b d s Y B₀ r' v q k N q' ε incoming paid
  have input := H.laws.intake
  have len : S.patch.L=L := H.laws.data.funds.length_eq
  have hg : 0 < gStep R.beta := inv_pos.mpr (Real.sqrt_pos.mpr input.positive)
  let σ := scroll H M κ hhalo
  obtain ⟨w,hw,hpaid⟩ := Release.chorus (q:=q') (d:=ε) (labels:=plate H) σ
    (fun _ => rfl) hG (hp.symm ▸ hQ) hplays (len.symm ▸ hA) hr hg.le (len.symm ▸ hC)
    (fun i => show (σ i).Played n (gStep R.beta) (M.ε*R.p.threshold) from
      ⟨fun _ => guard_silent κ hg (mul_pos M.guards R.p.threshold_pos)⟩)
    input.cap.labels.regular paid
  have principal i : B.Regular (plate H i).support (announced H M q' κ ε i) ∧
      B.supBounds (plate H i).site (plate H i).support (announced H M q' κ ε i) (w i) :=
    (arithmetic H M q' κ ε hhalo i).symm ▸ hw i
  obtain ⟨τ,hτ,anchored,cap⟩ := tighten R paid input.cap.labels.boundE
  have charge : 0 ≤ incoming := budget_nonneg (anchored (R.activities.reg 0).site)
  refine ⟨⟨w,principal,by rwa [len] at hpaid⟩,fun i => τ i * |E x|,?_,?_⟩
  · intro z
    have ledger := landing H hhalo B hplays hr ht hA (fun i => (hτ i).1) incoming
      anchored |E x| (abs_nonneg _) z
    exact budget_loosen ledger (mul_le_mul_of_nonneg_right ((le_abs_self (cost x)).trans small) charge)
  · intro i
    have order : B.order ≤ j := hplays.rehearsed.test.le.trans hj
    refine ⟨legal H M q' κ χ ε hplays i N order (principal i).1, fun cover =>
      Brim.round H M q' κ χ ε hplays i N order hr (principal i).1
        (mul_nonneg (hτ i).1 (abs_nonneg _)) cover ?_⟩
    intro U hU z hz T' hd hα
    simp only [Function.comp_def,glyph]
    simp_rw [lily]
    apply average H (κ:=κ) q' ε N hplays i T' hU hG (hτ i) (E x)
    intro F Y'
    have manifest : (foyer H i F χ U Y').manifest := planted_valid (Greenbelt.prism T x χ o.K U F) _
    exact hx c f S T hS hs R Q μ α H F _ i rfl rfl rfl rfl manifest B hr hp hplays
      (plate H i).support (Key (R.activities.reg i).support x F) (mapcase H i F) q' ε (τ i)
      _ (plate H i).anchor (hr ▸ cover) hU (grove H i Y' F hU hplays.rehearsed.temp_eq)
      (hτ i) (by simpa [len] using cap i) z hz T' hd (hp ▸ hα)

end YM.Integration.QLocalInheritedRelativeGlyph
end
