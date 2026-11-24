import YM.Integration.FVA1Physical.Sources.Round2.TwoPhysicalFields
import YM.Integration.FVA1Physical.Wilson.FluctuationSharp

/-! Buy the two adjacent thermal sectors in their actual axes and use one
realized scene to form both blocking kernels. The sole nonlocal term in the
conclusion is the actual signed exterior covariance. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Function Filter Set Finset MeasureTheory Lattice RG YM.Wilson Tree Precision Exterior
open MSbar MSbar.Heath MSbar.Heath.Cottage MSbar.Heath.Stock MSbar.Bulk MSbar.Lis MSbar.Mosaic
open Comparison.RG02 MSbar.Midpoint MSbar.Whisk MSbar.Rolling MSbar.Bakery MSbar.Bakery.Film MSbar.Cacao Push.Uniform
open Push.AbsoluteSums ConnectedActivityE6 Pressure Comparison.RG02.Order RGComparison.Core16 RGComparison.Core16.Spool
open YM.Integration.FVA1Physical.Wilson Progress.DirectedRecipe Next.SectorChange PhysicalNext.Repeat.Legato
open scoped Classical Topology BigOperators
variable {G : Gauge} {ι : Type} [Fintype ι] (J : ι → Lamp G)

private theorem season_admits {c f : Side} {S : StepData c f} {R : Rep G f} {P : Rep G c}
    {Q : Voice G} {H H' : Stage} {x val : ℝ} (h : Season Q H H' x R P S val) :
    ∀ V, Admitted V R S H'.width H'.paths (ability (tip G S.patch.L x)) (lbt (tip G S.patch.L x)) 1 :=
  fun V=>⟨h.case_.lawful,fun U=>(h.shine U).le,push_strict S R.beta h.bends.1 h.shine
    ((R.envelope h.case_.lawful).integrable _) V,S.isKernel h.bends.1 _⟩

theorem two_thermal_seasons (V : Voice G) (cle : Clear G V) (χ : ChartRatio G) (hχ : LocalRatio χ)
    (simple : G.Simple) (H H' H'' : Stage) (P₀ P₁ : Patch) (K₀ K₁ : KernelChoices)
    (h₀ : P₀.Branches K₀ G) (h₁ : P₁.Branches K₁ G) (p s L : ℕ) (part : Bool) {D η : ℝ}
    (hD : 0 ≤ D) (hη : 0 < η) (hp : η < (p:ℝ)+1) (exp : ℝ) : ∃ pal : Palisade,
    ∀ᶠ x : ℝ in atTop, ∀ {C : Family G} (chain : Comparison.RG02.Bulk.Chain C.path)
      {N n j r : ℕ} (T : Scene C.path.levels n r) (F : Forest (C.path.levels.clock.op j n).ratio)
      (v : (C.path.levels.clock.op j n).Choices) (F' : Forest (C.path.levels.clock.op (j+1) n).ratio)
      (v' : (C.path.levels.clock.op (j+1) n).Choices),
      let B:=sceneIssue (N:=N) chain T F v
      let A:=sceneIssue (N:=N) chain T F' v'
      let y:=tip G P₀.L x
      let z:=tip G P₁.L y
      B.S.patch=P₀ → B.S.kernel=K₀ → Season V H H' x B.pre B.post B.S (courage G P₀.L x) →
      A.S.patch=P₁ → A.S.kernel=K₁ → Season V H' H'' y A.pre A.post A.S (courage G P₁.L y) →
      Kind A.T → Expanse A.T 1 (p+2) → Alto.Wedge A.T Alto.Dean (hatW z) (Alto.cWidth z) s (p+2) →
      Premier (main A.f A.pre.clip A.pre.path) → Critical A.F A.pre.clip A.pre.path A.ρ →
      (mold A.pre A.F A.v).PosDef →
      ∀ (b : Site B.f) (Z : Positions (Primary B.c G)) (b' : Site A.f) (o : ι → Site A.f),
      ‖Z‖ ≤ D*room y → (∀ i : Slice J, separation b' (legs J o i).1 ≤ L*closeN z) →
      (∀ X : Positions (Primary A.c G), ‖A.fClock • X‖ ≤ (2*fluctuationFee pal V D)*room z →
        FieldPort A χ V (p+2) L J part z (z^pawn (p+2)) b' X) →
      let O:=represent (tint G (Body 1 B.c) Z)
      let μ:=vest (priced B.F B.v B.pre.clip B.pre.path) Z
      let live:=hotel B.F (boxX y b) (boxY y b) V O μ (pillow y) (room y)
      let copy:=chambers B.F (boxY y b) V O μ
      let E:=expect B.S B.pre O
      |E (boundaryStencil J A o part)-E (live.indicator (independentStencil J A χ p o part ∘ copy))| ≤
        stencilBound J*y^exp + |E (live.indicator (fun U => externalScores J A o part (canoe (S:=B.S) B.F U) (copy U)))| +
          A.fClock^((p:ℝ)+1-η) := by
  obtain ⟨pal,purchase⟩:=purchased_fluctuation_chance V cle simple H H' P₀ K₀ h₀ hD exp
  have fee : 0 ≤ fluctuationFee pal V D := by
    unfold fluctuationFee ceilingP
    have h:=zero_le_one.trans cle.cost; have t:0 ≤ shade G:=(shade_pos G).le; positivity
  let Bnd:=2*fluctuationFee pal V D
  have bnd : 0 ≤ Bnd := mul_nonneg zero_le_two fee
  have applyInner:=fluctuation_field_season J V cle χ hχ simple H' H'' P₁ K₁ h₁ p s L part bnd hη hp
  have growth:=Work.E09.betaF_growth G P₀.L
  refine ⟨pal,?_⟩
  filter_upwards [purchase,growth.eventually applyInner,growth.eventually (thermal_step simple P₁)]
    with x outerOffer innerOffer compare
  intro C chain N n j r T F v F' v' B A y z p₀ k₀ out p₁ k₁ inn kind plane wedge prem crit pd b Z b' o hZ loc ports O μ live copy E
  obtain ⟨_,money,window,_⟩:=outerOffer B p₀ k₀ out Z b hZ
  have hb : 0 < B.fClock := inv_pos.mpr (Real.sqrt_pos.mpr ((half_pos (zero_lt_one.trans out.case_.enough)).trans_le out.case_.beta))
  have ha : 0 < A.fClock := inv_pos.mpr (Real.sqrt_pos.mpr ((half_pos (zero_lt_one.trans inn.case_.enough)).trans_le inn.case_.beta))
  have price := innerOffer A p₁ k₁ inn kind plane wedge b'
  exact two_step_fields J A χ p L o part b' z η Bnd loc inn.bends.1 prem crit pd ha
    (fun X hx => price X hx (ports X hx)) (season_admits inn) B.S B.pre O (season_admits out O) B.F (boxX y b) (boxY y b) V μ cle
    money.first.extendsX y (y^exp) money.sails
    (fun U hU=>regularInputs_thermal (copy U) hb ha fee compare (window U hU))

end YM.Integration.FVA1Physical.Round2.Curvature
