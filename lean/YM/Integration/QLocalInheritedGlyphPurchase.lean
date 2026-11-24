import YM.Integration.QLocalInheritedRelativeGlyph
import YM.Integration.WilsonLimitConstruction.FundedCompanySelection

/-! Purchase the unweakened singleton glyph on the physical company's own
    canonical menu. Its original stages and lengths are retained. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalInheritedGlyphPurchase
open Function Filter Set Lattice RG Pressure Pressure.Testing Tree Wilson
open PhysicalNext PhysicalNext.Repeat PhysicalNext.JointLoad
open ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.Blaze.March
open AnalyticBridge VerifiedReset Precision Supply Input Org
open Push Push.PriceCompiler Push.SectorMeasure Next.Scheduling
open JointLoad.Heir JointLoad.Psalm JointLoad.Clockwork
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open scoped Topology BigOperators Classical
variable {G : Gauge}

def Chart {P : Teller G} {W : ℝ} {n : ℕ}
    (Q : Target G P) (o : Target.Order G W) (M : Heir.Record) (C : Libretto G n)
    (t v : ℝ) (r p : ℕ) (κ : Chi) (L : Side) (x γ : ℝ) : Prop :=
  ∀ {c f : Side} {S : StepData c f} (T : Tube G S), Works P L x S T →
    ∀ (R : Rep G f) (μ α : ℝ) (H : Cash W x μ L Q o α T R) (B : BudgetPoint),
    B.B = radiusB x → B.power = p → Plays C M B R.p P T x → Q.halo+5 ≤ r →
    Release.accepts r R.p.supportExponent t L →
    Release.Quotation C p r R.p.supportExponent t v →
    Lute.Plented C M B R.p L r x (gStep R.beta) → ∀ j ≥ n,
    ∀ (C' d h Y A b r' B₀ q : ℝ) (k : ℕ),
    Captain H j C' d h Y A b r' B₀ q k Chi.canonical → ∀ q' ε (incoming : ℝ),
    R.activities.EBound R.p incoming → Brim.Houses H M q' κ Chi.canonical ε B t
      (v / L.val * incoming) (betaF G x L ^ γ * incoming)

theorem charts (hG : G.Simple) {P : Teller G} (Q : Target G P) {W : ℝ}
    (o : Target.Order G W) {n : ℕ} (M : Heir.Record) (C : Libretto G n)
    (t v : ℝ) (r p : ℕ) (κ : Chi) (L : Side) (γ : ℝ) (hγ : -(1/2 : ℝ) < γ)
    (hM : M.ε ≤ 1/4) (hn : 2 ≤ n) (ht : 0 ≤ t) :
    ∀ᶠ x in atTop, Chart Q o M C t v r p κ L x γ := by
  by_cases h : ∃ D : Patch, D.L=L ∧ D.J=P.j ∧ D.Branches P.bind G
  · obtain ⟨D,hL,hJ,hD⟩ := h
    filter_upwards [QLocalInheritedRelativeGlyph.issue G hG P L D hD p n C M hM hn
      Chi.canonical κ W o t r ht γ hγ] with x hx c f S T hs R μ α H B hB hp hh hQ
      ha hq hu j hj C' d h' Y A b r' B₀ q k N q' ε incoming paid
    exact hx c f S T (hs.patch hL hJ) hs R Q μ α H B hB hp hh hQ v ha hq hu j hj
      A b d Y C' B₀ r' h' q k N q' ε incoming paid
  · exact Eventually.of_forall fun x c f S T hs =>
      (h ⟨S.patch,hs.length_eq,hs.funds.atStep,hs.funds.kernel⟩).elim

def Paid (γ : ℝ) {M : Metals G} {D : Rolls M.p} {A : Alloy M D}
    (R : Roost.Factor A) : Prop :=
  ∀ j x, A.delay.betaEntry j ≤ x → ∀ i, StepStages j i → M.p.first ≤ i →
    Chart (R.target j i) (R.shape.o j i) (R.recordP j i) (R.prices j i)
      (Solo.raise R.t j i) (R.v j i) (R.span j i) (M.p.profile i).power
      (Roof.wind R.menu j i) (D.L j) x γ

def CanonicalPrice (γ : ℝ) : Prediction G := fun {_} {_} {_} R =>
  Roof.wind R.menu = (fun _ _ => Chi.canonical) → Paid γ R

/-- Each transition is bought once before the actual protection is used,
    with the original changes of period and the original stage register. -/
theorem prepaid (hG : G.Simple) (γ : ℝ) (hγ : -(1/2 : ℝ) < γ)
    (s : Sheet G) (price : MapPrices) : Prepaid (CanonicalPrice γ) s price := by
  intro Q E _ C z _ _
  refine ⟨fun _ => 0, fun l _ D w U Z _ _ θ M _ V hM => ?_⟩
  let P (j i : ℕ) (x : ℝ) := Chart (Q j i) (Z.o j i) (M j i) (C j i)
    (Solo.raise (Roof.rays s) j i) (z j i) (Roof.mile j i) (s.profile i).power
    Chi.canonical (D.L j) x γ
  have stage j i (he : StepStages j i) : ∀ᶠ x : ℝ in atTop, s.first ≤ i → P j i x := by
    by_cases hi : s.first ≤ i
    · have ht : 0 ≤ Solo.raise (Roof.rays s) j i :=
        add_nonneg (add_nonneg (s.profile i).price_pos.le (by norm_num)) zero_le_two
      filter_upwards [charts hG (Q j i) (Z.o j i) (M j i) (C j i)
        (Solo.raise (Roof.rays s) j i) (z j i) (Roof.mile j i) (s.profile i).power
        Chi.canonical (D.L j) γ hγ (hM j i he hi)
        (le_trans (by decide) (s.profile i).order_ge) ht] with x hx _
      exact hx
    · exact Eventually.of_forall fun _ hi' => (hi hi').elim
  obtain ⟨β,_,hv,hβ⟩ := collect_upper V.betaEntry _
    (fun j => eventually_transitions j _ _ (stage j))
  refine ⟨{V with betaEntry := β},⟨hv,le_rfl,le_rfl,le_rfl⟩,?_⟩
  intro W hW K I hp B A η q E' X J K' b hZ hY hm menu j x hx i he hi
  change Roof.wind X = (fun _ _ => Chi.canonical) at menu
  change Chart (Q j i) (Z.o j i) (M j i) (C j i) _ _ _ _ (Roof.wind X j i) _ _ _
  rw [menu]
  exact hβ j x ((hW.beta j).trans hx) i he hi

end YM.Integration.QLocalInheritedGlyphPurchase
end
