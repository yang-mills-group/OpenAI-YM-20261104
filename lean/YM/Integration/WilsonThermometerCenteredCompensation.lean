import YM.Integration.WilsonThermometerCenteredAlgebra
import YM.Integration.WilsonFiniteOrdinaryInverse

/-! The inverse fees of the filed compensation on the actual three-source Wilson post. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerCenteredCompensation
open FVA1 Finset Function MeasureTheory Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6
open Laurent Stationary Comparison.RG02 Comparison.RG02.Order Filter OriginalForcedAddresses
open Table Extraction Climb Trace.Pilot Next.Rank Next.UVStress RG12 RG17 RG16.Literal
open WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource WilsonThermometerCourseIntake
open WilsonThermometerCourseHearing WilsonThermometerCenteredAlgebra Primitives.GCC.Anchor WilsonFiniteOrdinaryInverse
open scoped Classical BigOperators Topology
local notation "J" => Stock.census (Fin 3)
private def flip : (J).Mode ≃ (J).Mode where
  toFun := complement
  invFun := complement
  left_inv s := by apply Subtype.ext; ext i; simp [complement]
  right_inv s := by apply Subtype.ext; ext i; simp [complement]

theorem faces (Q : Poly J) (w : Fin 3→ℝ) (g : ℝ) (gp : 0<g) (small : g≤1)
    (loss : ℕ) (radii : ∀ t : (J).Mode, g^loss≤Poly.toll w t)
    (price : Poly.price (fun v=>g*w v) (inverseMass Q) ≤ fee J) :
    g^(3+loss)*(∑ s : (J).Mode, ‖weight Q s‖) ≤ fee J := by
  rw [mul_sum]
  calc _ ≤ ∑ s : (J).Mode,Poly.toll (fun v=>g*w v) (complement s) * ‖weight Q s‖ := by
          apply sum_le_sum
          intro s _
          rw [scaled,pow_add]
          have cards : (complement s).val.card≤3 := by simpa using Finset.card_le_univ (complement s).val
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul (pow_le_pow_of_le_one gp.le small cards) (radii _) (pow_nonneg gp.le _)
              (pow_nonneg gp.le _)) (norm_nonneg _)
       _ = Poly.price (fun v=>g*w v) (inverseMass Q) := Equiv.sum_comp flip (fun s : (J).Mode =>
          Poly.toll (fun v=>g*w v) s*‖(inverseMass Q).part s‖)
       _ ≤ fee J := price

theorem original {G : Gauge} (R : Run G) (simple : G.Simple)
    (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (φ : ℕ → ℕ)
    (width : ∀ a k : ℕ, k ≤ a → ∀ b : ℝ, R.alloy.delay.betaEntry a ≤ b →
      Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon k) a)⁻¹ ^ 2) ≤ b)
    (order shelf k seats depth : ℕ) (H cap : ℝ) (hc : 0 ≤ cap) :
    ∀ᶠ i : ℕ in atTop, ∀ (A : Group R.family 6) {m N per : ℕ} (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
      (_fit : k ≤ R.alloy.B.a.clock.J i) (tab : D.Tab R.rolls)
      (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j,RG.Rep G (R.family.side j per))
      (_course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
      (books : Mentor.Offices.Books D R.rolls tab φ) (law : VowsR.LawScroll G φ)
      (_enrolled : VowsR.Chamber law R.kit D tab books) (_fund : Volume.Fund D R.rolls tab φ books R.alloy.delay)
      (hi : m ≤ i) (live : i < N) (o : Positions (Fin 3) (R.family.side N per))
      (ahead : Mentor.Forecast D R.rolls tab φ books)
      (P : WilsonOriginalReceivedChain.Post (N:=N) R hk D tab π Γ Ψ books ahead disks sectors
          (fun u : Fin 3 => (grade u).val) order shelf seats i hi (offered R A simple live o))
      (a : Stationary.Link G (R.family.side i per)),
      let g := Coat.gStep (R.family.path.rep N per (i+1)).beta
      let B := R.family.path.levels.budget i
      let b := R.family.path.levels.clock.hatBeta i
      let angle := Stationary.arm G (R.family.side i per) 1 a
      ∀ z : ℝ, |z| ≤ |H| * (Real.log b)^depth*((B.B:ℝ)^2*B.threshold)/g →
        (∀ e, ‖Exterior.collect G angle e‖ ≤ cap*|z|) →
        ∀ (F : Forest (R.family.path.levels.clock.op i per).ratio) (tag : (R.family.path.levels.clock.op i per).Choices),
        let bank := Air.craft P.model (fun h => (P.model h).paint fired) (fun u : Fin 3 => (grade u).val)
          (π (i+1)) (AllOrder.Floe.Step.tape (Burn.horizon k+2))
        let W := Bulk.Fk ((RunFormalChain.fromRun R).step N i per live) F tag bank angle order
        let Q := Order.value (g:ℂ) (Order.ratio W)
        Poly.price (fun v=>g*P.w v) (inverseMass Q) ≤ fee J ∧
          ∀ loss : ℕ, (∀ t : (J).Mode, g^loss ≤ Poly.toll P.w t) →
            g^(3+loss)*(∑ s : (J).Mode, ‖weight Q s‖) ≤ fee J := by
  filter_upwards [WilsonReceivedLogWindow.original R simple D φ width (fun u : Fin 3 => (grade u).val)
      order shelf k seats depth H cap hc,WilsonReceivedTaylorWindow.potential R simple depth H]
    with i income window
  intro A m N per hk fit tab π Γ Ψ course books law enrolled fund hi live o ahead P a g B b angle
    z hz inside F tag bank W Q
  have earn := income hk fit tab π Γ Ψ course books law enrolled fund hi live ahead disks sectors
    (offered R A simple live o) P fired a z hz inside F tag
  have cheap : g≤1 := (window N per live z hz).1
  have gp : 0 < g := inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson live))
  have price := WilsonFiniteOrdinaryInverse.inverse W (Bulk.fk_unit ..) (Bulk.fk_sym ..)
    P.w P.salary.positive g gp cheap (fun s=>(earn s).1)
  exact ⟨price,fun loss radii=>faces Q P.w g gp cheap loss radii price⟩

end YM.Integration.WilsonThermometerCenteredCompensation
