import YM.Integration.WilsonThermometerUnitFilingFlatFaces
import YM.Integration.WilsonCapturedPrimaryPublishedPost

/-! The complete signed pupil at the earlier flat field compared with its actual finite normalized Wick program. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingFlatMaterial
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

theorem original {G : Gauge} (R : Run G) (simple : G.Simple)
    (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (φ : ℕ → ℕ)
    (width : ∀ a k : ℕ, k ≤ a → ∀ b : ℝ, R.alloy.delay.betaEntry a ≤ b →
      Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon k) a)⁻¹ ^ 2) ≤ b)
    (grades : Fin 3 → ℕ)
    (order shelf k slots q : ℕ)
    (deep : 2*(q+1+3+1)+8≤order) (aged : q+1+3+4≤3*k+2) :
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
      (P : WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades
        order shelf slots i hi physical) (x : Wallet actors),
      let g := Coat.gStep (R.family.path.rep N per (i+1)).beta
      ∀ (F : Forest (R.family.path.levels.clock.op i per).ratio) (tag : (R.family.path.levels.clock.op i per).Choices),
        let issued := Air.craft P.model (fun j => (P.model j).paint x) grades (π (i+1))
          (AllOrder.Floe.Step.tape (Burn.horizon k+2))
        let W := Bulk.Fk ((RunFormalChain.fromRun R).step N i per cut) F tag issued 0 order
        let student := Oak.student (n:=per) R hk D Q π Γ books hi P.op P.lesson ahead actors P.model order P.voter
        let read := WilsonRootedKioskOccupiedSlip.bare (rendered student (Ψ i).p g) x (1:Config G (R.family.side i per))
        ∀ (withdrawal:Poly (J)) (s:(J).Mode),
          Poly.toll (fun v=>g*P.w v) s*
            ‖(total (Poly.pass read) withdrawal).part s-(total (Order.value (g:ℂ) (Order.ratio W)) withdrawal).part s‖ ≤
            ((Fintype.card (J).Mode:ℝ)*(WilsonReceivedCloseOrdinaryGrade.invoice (J) 3 0 q 1*g^(q+1)))*
              Poly.price (fun v=>g*P.w v) (inverseMass withdrawal):=by
  filter_upwards [WilsonCapturedPrimaryPublishedPost.original R simple D φ width grades order shelf k slots 0 q 3 deep aged
    0 0 (le_refl _),WilsonReceivedTaylorWindow.potential R simple 0 0] with i posted cooled
  intro m N per hk fit Q π Γ Ψ course books law chamber funds hi cut ahead X _ _ actors pieces physical P x
    g F tag issued W student read withdrawal s
  have cool:g≤1:=(cooled N per (by omega) 0 (by simp)).1
  have gp:0<g:=inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson cut))
  refine WilsonThermometerUnitFilingFlatFaces.complete P.w P.salary.positive gp cool (Poly.pass read)
    (Order.value (g:ℂ) (Order.ratio W)) withdrawal s (WilsonReceivedCloseOrdinaryGrade.invoice J 3 0 q 1*g^(q+1)) ?_
  intro t
  let angle:=Stationary.arm G (R.family.side i per) 1 (0:Stationary.Link G _)
  have angleZero:angle=0:=map_zero _
  have groupZero:Integral.sample g angle=1:=(congrArg (Integral.sample g) angleZero).trans (sample_zero G _ g)
  have clear:flags (Ψ i).p.threshold (Integral.sample g angle)=∅:=groupZero ▸ flag_free _ _ _
  have get:=posted hk fit Q π Γ Ψ course books law chamber funds hi cut ahead actors pieces physical P x
    (0:Stationary.Link G _) 0 (by simp) (by simp [Exterior.collect]) F tag clear t
    (Finset.card_le_univ t.val |>.trans_eq (Fintype.card_fin 3))
  rw [map_zero,sample_zero] at get
  change Poly.toll P.w t*‖(Poly.pass ((rendered student (Ψ i).p g).log x 1)).part t -
    (Order.value (g:ℂ) (Order.ratio W)).part t‖ ≤ _ at get
  let hear:Poly (J)→ℝ:=fun row=>Poly.toll P.w t*‖(Poly.pass row).part t-(Order.value (g:ℂ) (Order.ratio W)).part t‖
  have replace:=congrArg hear (WilsonThermometerUnitFilingFlatFaces.unmasked (rendered student (Ψ i).p g) x)
  exact replace.ge.trans get

end YM.Integration.WilsonThermometerUnitFilingFlatMaterial
