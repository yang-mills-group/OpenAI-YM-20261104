import YM.Integration.WilsonIndependentCollarNeutralIncome
import YM.Integration.WilsonThermometerUnitFilingWeakFirstScore
import YM.Integration.WilsonThermometerUnitFilingWeakVertexSpoke

/-! A chronological Gaussian contraction of the independently filed finite
board consumes two legs. Its factor is elected on the same unmarked Wilson
history before cutoff and period, including for a nonconstant output. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonIndependentCollarWickIncome
open Filter Function Finset Lattice Laurent Bloch Precision RG Next.Free Work.F08 Wilson FormalBulk08 Flat
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Winding WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Soil WilsonCoeffUV.Mer WilsonCoeffUV.Cosmos WilsonCoeffUV.Blue WilsonCoeffUV.Embroider
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonThermometerUnitFilingWeakPair (mass booked)
open scoped Classical BigOperators
variable {G : Gauge} {U E : Type} [Fintype U] [NormedAddCommGroup E] [NormedSpace ℝ E]

def multiplicity : ℕ → ℕ → ℝ
  | 0, _ => 1
  | t+1, r => ((t+1:ℕ):ℝ)⁻¹ * (((r+1:ℕ):ℝ)*((r+2:ℕ):ℝ)/2) * multiplicity t (r+2)

private theorem scale (w : U → ℝ) (r : ℕ) (t : ℝ) (P : Ten E U r) :
    mass w r (t • P) = |t| * mass w r P := by
  induction r with
  | zero => exact norm_smul t (P Fin.elim0)
  | succ r ih =>
    have h (a : U) : prune (t • P) a=t • prune P a := rfl
    simp only [mass,h,ih,mul_sum]
    exact sum_congr rfl fun _ _ => by ring

theorem heat (w : U → ℝ) (w₁ : ∀ u,1≤w u) (C : Matrix U U ℝ) {z : ℝ} (positive : 0≤z)
    (issued : ∀ a b, |C a b|≤z) (P : Gen E U) (t r : ℕ) :
    mass w r (iceberg C P t r) ≤
      multiplicity t r * z^t * mass w (r+2*t) (P (r+2*t)) := by
  induction t generalizing r with
  | zero => simp [iceberg,multiplicity]
  | succ t ih =>
    let F : Gen E U := iceberg C P t
    have hp := booked w w₁ C z issued r F
    have next := ih (r+2)
    have same : r+2+2*t = r+2*(t+1) := by omega
    rw [same] at next
    have pos : 0≤((r+1:ℕ):ℝ)*((r+2:ℕ):ℝ)*(z/2) := by positivity
    change mass w r (((t+1:ℕ):ℝ)⁻¹ • ripple C F r) ≤ _
    rw [scale, abs_of_nonneg (by positivity : 0≤((t+1:ℕ):ℝ)⁻¹)]
    calc
      _ ≤ ((t+1:ℕ):ℝ)⁻¹ * (((r+1:ℕ):ℝ)*((r+2:ℕ):ℝ)*(z/2)*
           (multiplicity t (r+2)*z^t*mass w (r+2*(t+1)) (P (r+2*(t+1))))) :=
        mul_le_mul_of_nonneg_left (hp.trans (mul_le_mul_of_nonneg_left next pos)) (by positivity)
      _ = _ := by rw [multiplicity,pow_succ]; ring

abbrev price (_ : ℕ) (I : Gear G) : ℝ := nimbus I

omit [Fintype U] [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The physical gear buys the finite torus covariance at the actual paid
width. The exponent (t) counts Wick pairs, never unchanged dates. -/
theorem original (R : Run G) (simple : G.Simple) (fund : FundedMarkedCoverRows.prices price R.kit)
    (e : ℕ) : ∀ᶠ b : ℕ in atTop, ∃ Q : Realm G (e+1) Credit.leanC,
    Q.draws=R.family.path.levels ∧ Q.paid=R.metals.O ∧ Q.anchor=b ∧
    ∀ (j : ℕ), ∀ h : Q.anchor ≤ j, ∀ s : ℝ, ∀ hs : 0 < s,
      let I := holt Q j h s hs
      ∀ (ι : Type) [DecidableEq ι] (J : Finset ι) (D k : ι→ℕ) (p : PackOne J D k e I)
        (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
        (w : Site p.V.n × I.dial → ℝ), (∀ a,1≤w a) →
        ∀ (P : Gen E (Site p.V.n × I.dial)) (t r : ℕ),
          mass w r (iceberg p.N P t r) ≤ multiplicity t r *
            (Borough.ageZ (R.family.path.levels.clock.hatBeta j))^t * mass w (r+2*t) (P (r+2*t)) := by
  filter_upwards [FundedMarkedCoverRows.realm R simple price fund 0 (fun _=>0) (fun _=>1)
    (fun _=>Nat.zero_lt_succ _) e 0 0] with b paid
  obtain ⟨Q,levels,coins,calendar,anchor,_,_,_,stages⟩ := paid
  refine ⟨Q,levels,coins,anchor,?_⟩
  intro i hi s hs I ι dec J D k p E localGroup localSpace w w₁ P t r
  obtain ⟨_,_,money⟩ := stages i (anchor ▸ hi) hi
  have cost : I.mass≤Borough.ageZ (R.family.path.levels.clock.hatBeta i) := by
    change nimbus (Q.mint i hi).gear≤_
    simpa only [price,Realm.cash,Credit.lean_cost,calendar,Ticket.zz,Borough.ageZ] using money
  have row := (p.V.rateRamp.mono I.h.le).bow
  have bounded (a b : Site p.V.n × I.dial) : |p.N a b|≤I.mass := by simpa using row.2 a b
  exact heat w w₁ p.N (I.book.trans' zero_le_one |>.trans cost)
    (fun a b => (bounded a b).trans cost) P t r

end YM.Integration.WilsonIndependentCollarWickIncome
