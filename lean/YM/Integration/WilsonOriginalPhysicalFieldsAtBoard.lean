import YM.Integration.WilsonOriginalPhysicalCorridorAtBoard
import YM.Integration.WilsonOriginalCompactTrialTelescope

/-! The literal microscopic Wilson fields and the independently filed compact trial on the same decoder. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPhysicalFieldsAtBoard
open Function Finset Filter Lattice Wilson RG Tree Marker Multi QuadraticLocal Ac MeasureTheory
open Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit
open WheelP AnalyticBridge VerifiedReset PhysicalNext PhysicalNext.Repeat Legato
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open WilsonOriginalOccupiedStencil WilsonOriginalOccupiedCorridor WilsonThermometerMixedCollarSubpower
open WilsonPhysicalMarkedDefect.RegularProjection WilsonMeasuredCoefficientTransport
open Source Labels
open Pert.Asymptotics WilsonOriginalOccupiedWindow WilsonOriginalJointTrialHearing
open scoped Classical BigOperators

open WilsonRootedKioskOccupiedSlip
variable {G:Gauge}(R:Run G)(simple:G.Simple)
variable {V:Type}[DecidableEq V][Fintype V](marks:Marker.Census V)
local notation "H" j:max => R.family.path.levels.clock.hatBeta j

def microscopic {N per:ℕ}(vac:RG.Rep G (R.family.side N per))(d:V→ℕ)
    (Y:∀v,R.family.label (d v))(site:V→Site (R.family.side N per))(U:Config G (R.family.side N per)):Poly marks:=
  ((vac.eval U:ℂ)) • WilsonOriginalCompactTrialTelescope.product R marks d Y site U

def printed {n:Side}(vac:RG.Rep G n){X I:Type}{p:BudgetPoint}{o:V→Site n}
    (bank:Lamps X I G p o marks)(z:X)(U:Config G n):Poly marks:=(vac.eval U:ℂ) • Poly.pass (bare bank z U)

theorem inside {i per:ℕ}{vac:RG.Rep G (R.family.side i per)}{s:marks.Mode}{P:Slice R marks vac}
    {u:Config G (R.family.side i per)→Poly marks}(F:WilsonOriginalMountedRegular.Filing R vac P u s)(quiet:Envelope vac.eval):
    Integrable u (prior G _):=by
  letI : Countable F.I' := F.countNext
  rw [show u=_ from funext F.declared]
  exact WilsonOriginalOrdinaryBochner.unmasked vac quiet F.next F.hw' F.nextWidth F.other F.z
include simple in
theorem original (n cost a p desired debt ext raw w:ℕ)(np:0<n)(load:∀s:marks.Mode,s.val.card ≤ n)(e:ℝ)(ep:0<e)
    (order:desired+ext ≤ p)(reserve:desired+1+debt*n+2 ≤ p)
    (columns:∀ᶠ i:ℕ in atTop,(R.family.path.levels.params i).columns ≤ H i):
    ∃start:ℕ,∀(b N per m k L:ℕ),start ≤ b → m ≤ b+1 → ∀(live:b+1+L ≤ N),
    R.family.S.a (b+1)/R.family.S.a (b+1+L) ≤ (H (b+1))^cost →
    ∀(_way:WayStation R.kit)(D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
    (Q:D.Tab R.rolls)(π:ℕ → Layout G)(Γ:ℕ → Pace.Coin)(Ψ:∀j,RG.Rep G (R.family.side j per)),
    Concourse R.alloy R.kit R.T π Γ m N per k Ψ → TicketP R.alloy R.kit D Q →
    ∀(d:V→ℕ)(Y:∀v,R.family.label (d v))(site:V→Site (R.family.side N per))
    {T I:ℕ→Type}[∀i,Countable (I i)]{o:∀i,V→Site (R.family.side i per)}
    (bank:∀i,Lamps (T i) (I i) G (Ψ i).p (o i) marks)(test:∀i,T i)
    {wK:V→ℝ}{αK CK:ℝ},(∀v,0<wK v) → 0 ≤ αK →
    Gross (bank (b+1+L)) wK (Ψ (b+1+L)).p.B αK CK →
    ∀(P:∀j:Fin L,Slice R marks (Ψ (b+j.val+1))),
    (∀j:Fin L,(P j).A.density (P j).x=LocalComparison.actualPush R.family N per (b+j.val+1) (printed marks (Ψ (b+j.val+1+1)) (bank _) (test _))) →
    ∀(s:marks.Mode)(S:Fin L → V → ℝ),(∀j v,0 < S j v) → (∀j:Fin L,(WilsonOriginalOccupiedSalary.debit (P j).regular (P j).hard)^s.val.card ≤
      (H (b+j.val+1))^a*(Poly.toll (S j) s*Poly.toll (P j).w s)) →
    ∀W:Config G (R.family.side (b+1) per),WilsonOriginalMountedFailedHalo.board R N per (b+1) W →
    ∀{d₀:ℕ}{frame:Frame G d₀}(section_:SectionData frame)(group:Hol G)
    (F:∀j:Fin L,WilsonOriginalMountedRegular.Filing R (Ψ (b+j.val+1)) (P j) (printed marks (Ψ (b+j.val+1)) (bank _) (test _)) s),
    let enter:=read R N per W (show b+1 ≤ b+1+L by omega)
      (gust R.family.path N per N (microscopic R marks (Ψ N) d Y site) (b+1+L) live-printed marks (Ψ (b+1+L)) (bank _) (test _)) s
    let g:=regulatorRun R.family N per (b+1)
    let q:=desired+1+debt*n
    (∀j,Poly.toll (S j) s ≤ (g^ext)⁻¹) → (∀j,(F j).M ≤ (g^debt)⁻¹) →
    (∀j:Fin L,(R.family.path.levels.budget (b+j.val+1)).supportExponent ≤ 100) →
    (∀j,1 ≤ (F j).α ∧ (F j).h=WilsonOriginalMountedRegularFare.crop (q+1+w+raw) g) →
    (∀j,(F j).W ≤ (g^w)⁻¹ ∧ (F j).gross ≤ (g^raw)⁻¹ ∧ (F j).rent ≤ g^(q+1+w) ∧ (F j).δ ≤ g^(q+1)) →
    ‖read R N per W (show b+1 ≤ N by omega) (microscopic R marks (Ψ N) d Y site) s-
      (((R.family.path.rep N per (b+1)).eval W:ℂ)⁻¹)*(printed marks (Ψ (b+1)) (bank _) (test _) W).part s‖ ≤
      ‖enter‖+((4*(cost:ℝ)/Real.log 3)*WilsonOriginalOrdinaryFaceOrder.constant s s.val.card+e*(shards marks s).card)*g^desired:=by
  obtain ⟨start,heard⟩:=WilsonOriginalPhysicalCorridorAtBoard.original R simple marks n cost a p desired debt ext raw w np load e ep order reserve columns
  refine ⟨start,?_⟩
  intro b N per m k L age mb live ratio way D Q π Γ Ψ course ticket d Y site T I _ o bank test wK αK CK wp width sold
    rows sourced s S sp wages W board dim frame section_ group F
  let physical:=microscopic R marks (Ψ N) d Y site
  let trial (i:ℕ):=printed marks (Ψ i) (bank i) (test i)
  have hp:Integrable physical (prior G _):=WilsonOriginalCompactTrialTelescope.microscopic R marks (Ψ N)
    (WilsonOriginalFiledBochner.envelope R course (by omega) le_rfl) d Y site
  have ht (i:ℕ)(lo:b+1 ≤ i)(hi:i ≤ b+1+L):Integrable (trial i) (prior G _):=by
    by_cases last:i=b+1+L
    · subst i
      exact WilsonOriginalOrdinaryBochner.unmasked (Ψ _) (WilsonOriginalFiledBochner.envelope R course (by omega) live)
        (bank _) wp width sold (test _)
    · let j:Fin L:=⟨i-(b+1),by omega⟩
      have atDate:b+j.val+1=i:=by dsimp only [j];omega
      rw [←atDate]
      exact inside R marks (F j) (WilsonOriginalFiledBochner.envelope R course (by omega) (by omega))
  exact heard b N per m k L age mb live ratio way D Q π Γ Ψ course ticket physical hp trial ht rows sourced s S sp wages W board
    section_ group F

end YM.Integration.WilsonOriginalPhysicalFieldsAtBoard
end
