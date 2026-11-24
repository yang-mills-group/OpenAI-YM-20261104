import YM.Integration.WilsonReceivedChronologicalFixedPublicClock
import YM.Integration.WilsonReceivedChronologicalDates
import YM.Integration.WilsonReceivedChronologicalLastFlat
/-! An original before-cutoff appointment absorbs the fitted finite socket prices at the actual lower temperature. -/
set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalFixedRoseClock
open Finset Filter Function Lattice Wilson RG PhysicalNext.Repeat.Legato
open ActualRunAdmissionScales OriginalBareMarkedInvoice Pert.Asymptotics
open WilsonReceivedCanonicalVersePortfolio (wallet)
open WilsonReceivedChronologicalFixedPublicClock (roof)
open WilsonReceivedChronologicalLastFlat (wage)
open scoped Classical BigOperators Topology
variable {G:Gauge}{n:ℕ}(R:Run G)(simple:G.Simple)
local notation "H" i:max => R.family.path.levels.clock.hatBeta i

include simple in
theorem original : ∃start:ℕ,∀{m top N per:ℕ},start ≤ m+1 → m+1 ≤ N → ∀A:ℕ,
    R.family.S.scale top-R.family.S.scale m ≤ (A:ℝ)*(1+Real.log (H (m+1))) →
    ∀(grades:Fin n → ℕ)(S:Finset (Fin n))(target pole:ℕ)(B rent:ℝ),0≤B → 0≤rent →
      let g:=regulatorRun R.family N per (m+1)
      wallet R grades (fun _=>B*(H top)^pole) S*(rent*g^(target+2*pole*n)) ≤
        wallet R grades (fun _=>B*(roof (G:=G) A)^pole) S*(rent*g^target):=by
  obtain ⟨start,price⟩:=WilsonReceivedChronologicalDates.stages R simple 0
  refine ⟨start,?_⟩
  intro m top N per onset live A span grades S target pole B rent bp fee
  let g:=regulatorRun R.family N per (m+1)
  have mesh:R.family.S.a (m+1)/R.family.S.a (m+1+0) ≤ (H (m+1))^0:=by
    simp [(R.family.S.a_pos _).ne']
  have h:=(price (b:=m+1) (L:=0) (N:=N) (per:=per) onset (by simpa using live) mesh ∅
    (by simp) (by simp)).1
  have gp:0≤g:=h.1.le
  have small:g≤1:=by linarith only [h.1,h.2.1]
  have pos:0≤(H top):=le_trans zero_le_one (R.family.path.levels.fits.delayed top).le
  have absorb:=WilsonReceivedChronologicalFixedPublicClock.restored R grades S pole target B (H top) g
    (roof (G:=G) A) bp pos gp small (WilsonReceivedChronologicalFixedPublicClock.clock R simple A m top N per live span)
  change _*(rent*g^_) ≤ _*(rent*g^_)
  calc
    _ = (wallet R grades (fun _=>B*(H top)^pole) S*g^(target+2*pole*n))*rent:=by ring
    _ ≤ (wallet R grades (fun _=>B*(roof (G:=G) A)^pole) S*g^target)*rent:=
      mul_le_mul_of_nonneg_right absorb fee
    _ = _:=by ring
end YM.Integration.WilsonReceivedChronologicalFixedRoseClock
end
