import YM.Integration.WilsonOriginalOccupiedChargedTrial

/-! Restore the financial incidence only at the actual names of each occupied face. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalOccupiedModeTrial
open Function Finset Filter Lattice Wilson RG Tree Marker Multi QuadraticLocal Ac MeasureTheory
open Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit
open WheelP AnalyticBridge VerifiedReset PhysicalNext PhysicalNext.Repeat Legato
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open WilsonOriginalOccupiedStencil WilsonOriginalOccupiedCorridor WilsonThermometerMixedCollarSubpower
open Pert.Asymptotics WilsonOriginalOccupiedWindow WilsonOriginalJointTrialHearing
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) (simple:G.Simple)
variable {V:Type} [DecidableEq V] [Fintype V] (marks:Marker.Census V)
local notation "H" j:max => R.family.path.levels.clock.hatBeta j
local notation "κ" j:max => LocalComparison.forcedDivisor R.family j

private def average (S:V→ℝ)(s:marks.Mode):ℝ:=(Poly.toll S s)^((s.val.card:ℝ)⁻¹)

omit [Fintype V] in
private theorem exactPower (S:V→ℝ)(pos:∀v,0<S v)(s:marks.Mode):
    (average marks S s)^s.val.card=Poly.toll S s:=by
  by_cases flat:s.val.card=0
  · have empty:=Finset.card_eq_zero.mp flat
    simp [Poly.toll,empty]
  have nz:(s.val.card:ℝ)≠0:=by exact_mod_cast flat
  rw [average,←Real.rpow_natCast,←Real.rpow_mul (Poly.worth pos s).le,inv_mul_cancel₀ nz,Real.rpow_one]

include simple in
theorem original (n d a p:ℕ)(np:0<n)(load:∀s:marks.Mode,s.val.card ≤ n)(C e:ℝ)(cp:0 ≤ C)(ep:0<e):
    ∃start:ℕ,∀(b N per m k L:ℕ),start ≤ b → m ≤ b+1 → ∀(live:b+1+L ≤ N),
    (∀j:Fin L,(j.val:ℝ) ≤ C*(1+Real.log (H (b+j.val+1)))^d) →
    ∀(_way:WayStation R.kit)(D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
    (Q:D.Tab R.rolls)(π:ℕ → Layout G)(Γ:ℕ → Pace.Coin)(Ψ:∀j,RG.Rep G (R.family.side j per)),
    Concourse R.alloy R.kit R.T π Γ m N per k Ψ → TicketP R.alloy R.kit D Q →
    ∀(physical:Config G (R.family.side N per)→Poly marks),
    Integrable physical (prior G _) →
    ∀(trial:∀j,Config G (R.family.side j per)→Poly marks),
    (∀i,b+1 ≤ i → i ≤ b+1+L → Integrable (trial i) (prior G _)) →
    ∀(P:∀j:Fin L,Slice R marks (Ψ (b+j.val+1))),
    (∀j:Fin L,(P j).A.density (P j).x=LocalComparison.actualPush R.family N per (b+j.val+1) (trial (b+j.val+1+1))) →
    ∀(s:marks.Mode)(S:Fin L → V → ℝ),(∀j v,0 < S j v) → (∀j:Fin L,(WilsonOriginalOccupiedSalary.debit (P j).regular (P j).hard)^s.val.card ≤
      (H (b+j.val+1))^a*(Poly.toll (S j) s*Poly.toll (P j).w s)) →
    ∀W:Config G (R.family.side (b+1) per),flags (Ψ (b+1)).p.threshold W=∅ →
    let enter:=read R N per W (show b+1 ≤ b+1+L by omega) (gust R.family.path N per N physical (b+1+L) live-trial (b+1+L)) s
    let rest:=∑j:Fin L,WilsonOriginalOccupiedJointEdge.ordinary R marks Ψ (N:=N)
      (show b+1 ≤ b+j.val+1 by omega) (P j) (trial (b+j.val+1)) s W
    ‖(read R N per W (show b+1 ≤ N by omega) physical s-
      (((R.family.path.rep N per (b+1)).eval W:ℂ)⁻¹)*(trial (b+1) W).part s)-enter-rest‖ ≤
      ((e*(regulatorRun R.family N per (b+1))^p)*(shards marks s).card)*
        ∑j:Fin L,Poly.toll (S j) s/WilsonOriginalOccupiedDateShare.weight j.val:=by
  obtain ⟨start,settle⟩:=WilsonOriginalOccupiedChargedTrial.original R simple marks n d a p np load C e cp ep
  refine ⟨start,?_⟩
  intro b N per m k L age birth live span way D Q π Γ Ψ course ticket physical hp trial ht P source s S sp wage W clear
  have money:∀j:Fin L,0 ≤ average marks (S j) s:=
    fun j=>Real.rpow_nonneg (Poly.worth (sp j) s).le _
  have pay (j:Fin L):(average marks (S j) s)^s.val.card=Poly.toll (S j) s:=exactPower marks (S j) (sp j) s
  have actual:=settle b N per m k L age birth live span way D Q π Γ Ψ course ticket physical hp trial ht P source s
    (fun j=>average marks (S j) s) money (fun j=>by simpa only [pay] using wage j) W clear
  simpa only [pay] using actual

end YM.Integration.WilsonOriginalOccupiedModeTrial
