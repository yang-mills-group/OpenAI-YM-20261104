import YM.Integration.WilsonThermometerUnitFilingFlatMaterial
import YM.Integration.WilsonThermometerUnitFilingFlatWithdrawal
import YM.Integration.WilsonThermometerFiniteConnectedCells
import YM.Integration.WilsonThermometerUnitFilingNamedFaces

/-! Cost of the signed flat thermometric terminal in fixed source units, including the genuine proper-face subtraction. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingFlatThermometer
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open scoped Classical BigOperators Topology

open Extra.Trajectories Primitives.GCC.Anchor WilsonThermometerCenteredAlgebra
open private flag_free sample_zero from YM.Integration.WilsonReceivedIdentityField
local notation "J" => Stock.census (Fin 3)

open WilsonFiniteOrdinaryInverse WilsonThermometerRegisteredCenteredInvoice WilsonThermometerCenteredScalar
open WilsonThermometerFiniteConnectedCells OPE.Therm Pert.Asymptotics WilsonPositionThermometerGradedSource
local notation "grades₀" => WilsonThermometerUnitFilingNamedFaces.grades

theorem original {G : Gauge} (R : Run G) (simple : G.Simple)
    (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (φ : ℕ → ℕ)
    (width : ∀ a k : ℕ, k ≤ a → ∀ b : ℝ, R.alloy.delay.betaEntry a ≤ b →
      Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon k) a)⁻¹ ^ 2) ≤ b)
    (order shelf k slots loss target : ℕ)
    (deep : 2*((target+loss+4)+1+3+1)+8≤order) (aged : (target+loss+4)+1+3+4≤3*k+2) :
    ∀ᶠ i : ℕ in atTop,
    ∀ {m N per : ℕ} (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
      (_fit : k ≤ R.alloy.B.a.clock.J i) (Q : D.Tab R.rolls)
      (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
      (_course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
      (books : Mentor.Offices.Books D R.rolls Q φ) (law : VowsR.LawScroll G φ)
      (_enrolled : VowsR.Chamber law R.kit D Q books) (_fund : Volume.Fund D R.rolls Q φ books R.alloy.delay)
      (hi : m ≤ i) (cut : i < N)
      (ahead : Mentor.Forecast D R.rolls Q φ books) {X : Fin 3 → Type}
      [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
      (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v))
      (physical : Wallet actors → Config G (R.family.side (i+1) per) → Poly (Stock.census (Fin 3)))
      (P : WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades₀
        order shelf slots i hi physical) (x : Wallet actors),
      let g := Coat.gStep (R.family.path.rep N per (i+1)).beta
      ∀ (F : Forest (R.family.path.levels.clock.op i per).ratio) (tag : (R.family.path.levels.clock.op i per).Choices),
        let issued := Air.craft P.model (fun j => (P.model j).paint x) grades₀ (π (i+1))
          (AllOrder.Floe.Step.tape (Burn.horizon k+2))
        let W := Bulk.Fk ((RunFormalChain.fromRun R).step N i per cut) F tag issued 0 order
        let student := Oak.student (n:=per) R hk D Q π Γ books hi P.op P.lesson ahead actors P.model order P.voter
        let read := WilsonRootedKioskOccupiedSlip.bare (rendered student (Ψ i).p g) x (1:Config G (R.family.side i per))
        ∀ (A:WilsonPositionThermometerCapStation.Group R.family 6),
          let actual:=measured R A (N,per) (fun _=>0)
          (∀v:Fin 3,‖WilsonThermometerCenteredScalar.read actual {v}‖≤1) → (∀v,g*P.w v≤1) →
          g^(loss+2)≤Poly.toll P.w full →
          g=Coat.gStep (Ψ (i+1)).beta ∧
          ‖(Poly.pass read*properInvoice actual 1).part full-
            (Order.value (g:ℂ) (Order.ratio W)*properInvoice actual 1).part full‖ ≤
            (23*(|(Fintype.card (J).Mode:ℝ)*WilsonReceivedCloseOrdinaryGrade.invoice (J) 3 0 (target+loss+4) 1| *fee (J)))*g^target:=by
  filter_upwards [WilsonThermometerUnitFilingFlatMaterial.original R simple D φ width grades₀ order shelf k slots
      (target+loss+4) deep aged] with i posted
  intro m N per hk fit Q π Γ Ψ course books law chamber funds hi cut ahead X _ _ actors pieces physical P x
    g F tag issued W student read A actual means cap unscaled
  have gp:0<g:=inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson cut))
  refine ⟨(congrArg Coat.gStep (course.1.walk (i+1) (Nat.le_succ_of_le hi) cut).beta).symm,?_⟩
  let bill:=WilsonReceivedCloseOrdinaryGrade.invoice (J) 3 0 (target+loss+4) 1
  let cost:ℝ:=(Fintype.card (J).Mode:ℝ)*(bill*g^(target+loss+4+1))
  have source:=WilsonThermometerUnitFilingFlatWithdrawal.original P.salary.positive gp (Poly.pass read)
    (Order.value (g:ℂ) (Order.ratio W)) actual loss unscaled cap means cost (fun s=>
      posted hk fit Q π Γ Ψ course books law chamber funds hi cut ahead actors pieces physical P x F tag s full)
  apply source.trans_eq
  change 23*(|((Fintype.card (J).Mode:ℝ)*(bill*g^(target+loss+4+1)))| *fee (J)/g^(loss+5))=
    (23*(|(Fintype.card (J).Mode:ℝ)*bill| *fee (J)))*g^target
  rw [←mul_assoc,abs_mul,abs_of_pos (pow_pos gp _),show target+loss+4+1=target+(loss+5) by omega,pow_add]
  field_simp [gp.ne']

end YM.Integration.WilsonThermometerUnitFilingFlatThermometer
