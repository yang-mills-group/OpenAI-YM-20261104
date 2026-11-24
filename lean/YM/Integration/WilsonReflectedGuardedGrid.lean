import YM.Integration.WilsonReflectedAppointedIncome
import YM.Integration.WilsonOriginalMicroscopicGuardedGridSchool
/-! The very same three measured matrices returned by the full native
microscopic reporter school fund the signed rotated arms and the original
independently displaced trial sections. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedGuardedGrid
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Extra.Histories.Relay
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open RG05Readout RG05Readout.Address RG05Readout.Records WilsonOriginalNullCorridor MergeProof MergeProof.Accent
open WilsonOriginalMicroscopicGuardedPage WilsonOriginalMicroscopicGuardedReporters WilsonReflectedFullPanel
open WilsonOriginalMicroscopicGuardedGridSchool
open scoped Classical
variable {G:Gauge}(R:Run G)
local notation "C₀" => R.family

theorem original (simple:G.Simple)(d:Fin 3→ℕ):∃floor:ℕ,∀(j:Fin 3→ℕ)(target:ℕ)(η:ℝ)(M:Fin 3→ℝ)
    (Y:∀a:Fin 3,ℕ×ℕ→(C₀).label (d a)),
    (∀a,floor≤j a) → Finished R d j target η M Y →
    ∀f n N p (part:∀a,j a≤f)(live:f+n≤N), (∀a,j a<N) →
    ∃A:∀a:Fin 3,(C₀).label (d a) ≃ₗ[ℂ] (C₀).label (d a),
      (∀a x,Arrived R (d a) (j a) (f+n) N p target (Nat.le_add_right_of_le (part a)) live η (A a) x) ∧
      (∀a,receipt R (d a) (j a) (f+n) N p target (Nat.le_add_right_of_le (part a)) live η (A a) (Y a (N,p)) (M a)) ∧
      Placed R d j Y f n N p live A:=by
  classical
  choose first offer using fun a:Fin 3=>eventually_atTop.mp (WilsonReflectedAppointedIncome.original R simple (d a))
  refine ⟨univ.sup first,?_⟩
  intro j target η M Y due school f n N p part high seen
  let before (a:Fin 3):j a≤f+n:=(part a).trans (Nat.le_add_right f n)
  obtain ⟨A,whole,rows,_⟩:=school.1 (f+n) before N p high seen
  refine ⟨A,whole,?_,school.2 f n N p part high A whole⟩
  intro a
  have cost:=offer a (j a) ((le_sup (mem_univ a)).trans (due a)) (f+n) N p target (before a) high η
    (A a) (Y a (N,p)) (M a) (whole a (full R (d a) N p (j a) (Y a (N,p))))
  exact cost (rows a).2.1

end YM.Integration.WilsonReflectedGuardedGrid
end
