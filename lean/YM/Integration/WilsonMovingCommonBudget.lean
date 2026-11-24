import YM.Integration.WilsonMovingCommonQuotation
import YM.Integration.WilsonOriginalHighPocket

/-! A common quotation for the original Factor and the stronger singleton on one register. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Roof
open Filter Function Set Lattice Wilson Pressure RG RG.Supply Input Precision Org
open Push.PriceCompiler Push.SectorMeasure Push.AbsoluteSums ConnectedActivityE6 AnalyticBridge.VerifiedReset
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open ThroughLaunch WilsonStartup Extra.Histories Next.Scheduling Next.Foundations UVNext.CouplingReset
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius

section
variable {G : Gauge} {Z : ChartRatio G}
theorem actualBudgetTwo (s : Sheet G) (K : MapPrices) (hZ : LocalRatio Z)
    (r : ℕ→ℕ→ℕ) (t₀ t₁ earn ε : Return.Wages) (Y : ℕ) (ht₀ : ∀ j i,0≤t₀ j i) (ht₁ : ∀ j i,0≤t₁ j i) (hEarn : ∀ j i,0≤earn j i) (he : ∀ j i,-(1/2:ℝ)<ε j i ∧ ε j i<0)
    (l : ℕ) (hl : 500≤l) :
    ∃ (f : ℕ→ℕ) (C : Programs s) (v : Return.Wages) (L : Targets s K) (E : Expenses L), s.floorL≤f ∧
      (∀ j i,(L j i).table=Z ∧ (L j i).halo=l ∧ (E j i).earn=earn j i ∧ (E j i).wanting=ε j i ∧ (E j i).degrees=Y) ∧
      ∀ g, f≤g → Base {s with floorL:=g} K Z C v t₀ r E ∧ Earlier {s with floorL := g} K C v (Solo.raise t₁) r := by
  obtain ⟨b,hb,hx⟩ := Psalm.Refit.first s K hZ
  obtain ⟨f,C,v,hf,hE⟩ := WilsonCommonQuotation.original s K r (Solo.raise t₀) (Solo.raise t₁)
    (fun i j=> add_nonneg (ht₀ ..) zero_le_two) (fun i j=> add_nonneg (ht₁ ..) zero_le_two)
  choose L E hL hQ hC hP hT using fun j i=> aim_budget hZ (Testing.query s K j i) (earn j i) _ Y l hl (hEarn j i) (he j i).1 (he j i).2
  obtain ⟨x,-,he,H⟩ := Planning.sponsors s K L E
  refine ⟨max b (max f x),C,v,L,E,hb.trans (le_sup_left),fun j i=>⟨hL j i,hT j i,hC j i,hP j i,hQ j i⟩,fun g hl => ?_⟩
  have hb : b ≤ g := (le_sup_left (b:=f ⊔ x)).trans hl
  have hf : f⊔x ≤ g := (le_sup_right (a:=b)).trans hl
  have hG : x≤g := (le_sup_right (a:=f)).trans hf
  obtain ⟨low,high⟩ := hE g ((le_sup_left (b:=x)).trans hf)
  refine ⟨?_,high⟩
  exact ⟨low,hx _ hb,
    (fun j i he Y hL=> H.1 j i he Y ((hG j).trans hL)),fun j i he Y hL=> H.2 j i he Y ((hG j).trans hL)⟩

end
end YM.PhysicalNext.Repeat.Roof
end
