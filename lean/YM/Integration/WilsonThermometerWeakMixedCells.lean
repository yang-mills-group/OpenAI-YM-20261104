import YM.Integration.WilsonThermometerWeakPanelBorn
import YM.Integration.WilsonThermometerReflectedColumns

/-! The left cylinder is the measured Vane field at its own station. The right is
the complete separately graduated displaced angular source on the same bare law. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakMixedCells
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
open Next.Rank.Price Next.Rank.Tapes.West Next.Rank.Station Next.Rank.East
open Further.CorrectedLift MergeProof MergeProof.East MergeProof.Accent
open PhysicalNext.Repeat.Legato YM.Integration.WilsonLimitConstruction YM.Integration.WilsonPositionThermometerStationNorm
open RG12 RG05Readout Native Address Many Records Harvest
open WilsonThermometerOwnOffsetField WilsonThermometerWeakPanelBorn WilsonThermometerSmallPanelRead
open scoped Topology BigOperators Classical
variable {G:Gauge} (R:Run G)
local notation "C" => R.family
local notation "A" => R.family.path.levels

theorem moved {d k m χ N p:ℕ} (r:Emblems C d) (hk:k≤N) (hχ:χ≤N) (hm:m≤χ)
    (v:Site ((C).side m p)) (z z₀:Site ((C).side N p))
    (u:(C).label d) (fee:ℝ) (inside:Interior ((center (C).S p hχ 0).chamber 0) (arm R r hk z₀ u))
    (wage:(center (C).S p hχ 0).rootTest ((C).beta N p) (arm R r hk z₀ u)≤fee)
    (margin:z-z₀∈(center (C).S p (hm.trans hχ) 0).margin v (3*Cells.span (C).S hχ p)):
    let T:=center (C).S p (hm.trans hχ) 0
    ∃Y, Interior (T.chamber 0) Y ∧ T.rootTest ((C).beta N p) Y≤fee ∧ T.copy v Y=arm R r hk z u:=by
  intro T
  obtain ⟨Y,hY,price,equal⟩:=Frontier6.Platform.moved_basis R.makes hχ hm v inside wage margin
  refine ⟨Y,hY,price,equal.trans ?_⟩
  funext U
  change ((C).S.a k:ℂ)^d*(C).O N p _ z₀ (Lattice.translate (z-z₀) U)=((C).S.a k:ℂ)^d*(C).O N p _ z U
  rw [R.family.translation];congr 2;abel

private theorem with_pair {N p:ℕ} (T:Tiling ((C).side N p)) (v:Fin 2→Site T.period)
    (apart:v 0≠v 1) (Y:Fin 2 → Config G ((C).side N p)→ℂ)
    (inside:∀i,Interior (T.chamber 0) (Y i)) (q:Fin 2→ℝ)
    (cash:∀i,T.rootTest ((C).beta N p) (Y i)≤q i):
    ‖moment ((C).beta N p) (fun U=>T.copy (v 0) (Y 0) U*T.copy (v 1) (Y 1) U)‖≤q 0*q 1:=by
  have distinct:Function.Injective v:=by intro i j h;fin_cases i<;>fin_cases j<;>simp_all
  have seen:=T.planted (seamless R.makes N p) v distinct Y inside
  simp only [Fin.prod_univ_two] at seen
  exact seen.trans (mul_le_mul (cash 0) (cash 1) (T.root_nonneg _ _) ((T.root_nonneg _ _).trans (cash 0)))

theorem original {d D:ℕ} (simple:G.Simple) (panels:WilsonReportingAbsoluteInletLiveRun.PanelDates R)
    (f:Extraction.Order) (H:(Cells.standard C).Hierarchy) (grade:Fin (D+1)) (ε:ℝ) (pos:0<ε):
    ∃ (P:Fin 3→Tapes.Panel D) (κ:ℝ),Checks (P 0).arc (P 1).arc (P 2).arc κ (trays D) D ∧
    ∀ a:Fin 3,∃ Q:ℝ,0≤Q ∧ ∀ᶠ k₀:ℕ in atTop,∀ᶠ N:ℕ in atTop,∃ late:k₀<N,∀ p m
      (small:m≤widthSky A (P a).arc k₀) (c₀ c₁:Site ((C).side m p)) (o z z₀:Site ((C).side N p))
      {D':ℕ} (V:Vane C D') (j:Fin (D'+1)) (w:(Cells.standard C).Field j),
    let hk₀:widthSky A (P a).arc k₀≤N:=(widerSky A (P a).arc k₀).trans ((beforeSky A (P a).arc k₀).trans late.le)
    let T:=center (C).S p (small.trans hk₀) 0
    j.val=grade.val → V.k=k₀ → V.checked f H D' →
    o∈T.margin c₀ (3*span (C).S hk₀ p) → c₀≠c₁ →
    ∀ (k χ:ℕ)(hk:k≤N)(hχ:χ≤N)(_:m≤χ)(r:Emblems C d)(u:(C).label d)(b q:ℝ),
    1≤b → 0≤q → 1≤(A).clock.monitor k → z-z₀∈T.margin c₁ (3*span (C).S hχ p) →
    ∀ (J:(C).label d≃ₗ[ℂ](C).label d), (∀x,((C).labels.level d).coeffSize (J x)≤2*((C).labels.level d).coeffSize x) →
    let F:=(C).labels.level d
    let T₀:=center (C).S p hχ 0
    let X:=fun i=>arm R r hk z₀ (WilsonThermometerWeakPanelExchange.refine C (shrink C k N p)⁻¹ b J (Size.axis F i))
    (∀ i,Interior (T₀.chamber 0) (X i) ∧ T₀.rootTest ((C).beta N p) (X i)≤q) →
    ‖moment ((C).beta N p) (fun U=>(C).O N p (V.wheel.atCut (N,p) j w) o U*arm R r hk z u U)‖≤
      (Q*((A).clock.hatBeta k₀)^ε*(cost C grade*‖w‖))*(q*((2*scaleCost C d)*F.coeffSize u)):=by
  obtain ⟨P,κ,checks,policy⟩:=WilsonThermometerReflectedColumns.original R simple panels f H D (fun _:Unit=>grade) ε pos
  refine ⟨P,κ,checks,?_⟩;intro a
  obtain ⟨money,positive,offer⟩:=policy a
  refine ⟨money (),positive (),?_⟩
  filter_upwards [offer] with k₀ wk
  filter_upwards [wk] with N later
  obtain ⟨late,due⟩:=later
  refine ⟨late,?_⟩
  intro p m small c₀ c₁ o z z₀ D' V j w hk₀ T matchGrade station stamped left distinct k χ hk hχ hm r u b q hb hq monitor right J forward F T₀ X basis
  obtain ⟨V₀,in₀,paid₀,cut₀⟩:=due p m small (fun _=>c₀) (fun _=>o) V (fun _=>j) (fun _=>w) (fun _=>matchGrade) station stamped (fun _=>left) ()
  obtain ⟨inside,wage⟩:=WilsonThermometerWeakPanelBorn.root R r hk z₀ χ hχ b hb monitor J forward u q hq basis
  obtain ⟨V₁,in₁,paid₁,cut₁⟩:=moved R r hk hχ hm c₁ z z₀ u _ inside wage right
  let Y:Fin 2 → Config G ((C).side N p)→ℂ:=![V₀,V₁]
  let c:Fin 2→Site ((C).side m p):=![c₀,c₁]
  let fees:Fin 2 → ℝ:=![money ()*((A).clock.hatBeta k₀)^ε*(cost C grade*‖w‖),q*((2*scaleCost C d)*F.coeffSize u)]
  have result:=with_pair R T c distinct Y (by intro i;fin_cases i;exact in₀;exact in₁)
    fees (by intro i;fin_cases i;exact paid₀;exact paid₁)
  have h₀:T.copy c₀ V₀=(C).O N p (V.wheel.atCut (N,p) j w) o:=cut₀
  have h₁:T.copy c₁ V₁=arm R r hk z u:=cut₁
  simpa only [Y,c,fees,Matrix.cons_val_zero,Matrix.cons_val_one,h₀,h₁] using result

end YM.Integration.WilsonThermometerWeakMixedCells
end
