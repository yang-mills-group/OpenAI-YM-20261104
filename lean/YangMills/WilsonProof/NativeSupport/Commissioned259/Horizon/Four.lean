import YangMills.WilsonProof.NativeSupport.Commissioned259.Horizon.Adapters
/-!
# Two-zone physical phase and Horizon gap through *old* projection on the reader.

First with bills on all fixed tuples, sufficient for expansion in any finite basis; used later
for the uniform bills on H fields.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flash259HorizonFork
open Function Finset Filter Set MeasureTheory Table Extraction Spec Arboreal OPE.Orbits
open scoped Topology Classical BigOperators
open Node Log
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)
    (P:Prescription F.sector.derivatives) {I J:Type}[Fintype I][Fintype J]{d:I→ℕ}{e:J→ℕ}
    (u:Labels S d)(v:Labels S e)
    (Z:PhysMS.tower S) (hG:G.Simple) (H:LogTrace F P)
    {M δ:ℝ}(mn:0≤M)(dp:0<δ)

local notation "nearSet" => near I J
local notation "tree" => Flash259HorizonFork.frame I J
local notation "bare" => Chart.bare
local notation "farSet" => outer I J
local notation "massₒ" r:max s:max => (r^(∑ i,d i)*s^(∑ j,e j))
local notation "ix" => Orbits.names u
local notation "iy" => Orbits.names v

include dp in
lemma indices (ζ r t x y o) (h:Ready r t M δ x y) :
    Call.demand F ζ (sites o r t x y) (tree).leaves (cards ix iy)=
      Orbits.whole (spectator F ζ) (atPosition o r x) u (atPosition o t y) v := by
  unfold Call.demand; rw [as_full _ (spectate F ζ).laws.toSymmetric,whole_observed]; exact profiles o h dp
include H mn dp hG Z in
theorem phases : ∃ k:ℕ, ∀ᶠ s in 𝓝[>] (0:ℝ), ∀ r x y o, Ready r s M δ x y → ∀ ζ ζ', massₒ r s *
    ‖Orbits.whole (spectator F ζ) (atPosition o r x) u (atPosition o s y) v -
      Orbits.whole (spectator F ζ') (atPosition o r x) u (atPosition o s y) v‖ ≤ 2*s*(badge s * badge r)^k := by
  obtain ⟨k,H⟩:= Call.phases F Z hG H (cards ix iy) mn dp; refine ⟨k,H.mono fun i h r x y o hi ζ ζ'=>?_⟩
  simp_rw [← indices F u v dp _ _ _ _ _ _ hi]
  exact h r x y o hi ζ ζ'

include H mn dp hG Z in
theorem billed (h:ℕ) : ∃ (L:ℝ) (k:ℕ), 0 ≤ L ∧ ∀ᶠ s in 𝓝[>] (0:ℝ),
    ∀ r x y o, Ready r s M δ x y → ∀ ζ, massₒ r s * ‖discrepancy (spectator F ζ) h
      (atPosition o r x) o u (shadowOld P h (atPosition o r x) o u) (atPosition o s y) v‖ ≤
      L*(badge s * badge r)^k*(s+(r/s)^(h+1)) := by
  obtain ⟨L,k,l,H⟩:= Call.original F Z hG H (cards ix iy) h mn dp; refine ⟨L,k,l,H.mono fun s H r x y o hi ζ=>?_⟩
  have T:=spectator F ζ; let Y:=sites o r s x y; let w:=cards ix iy
  have hS:=spectate F ζ; have hx:=profiles o hi dp; have hp:=center_profiles o hi dp
  rw [discrepancy_old _ _ _ _ _ _ _ hS (spectate_respects F ζ) (spectate_ready F ζ) hp, ← Orbits.whole_observed,← indices F u v dp _ _ _ _ _ _ hi]
  have e : P.truncated (spectator F ζ) h (atPosition o r x) ix o (atPosition o s y) iy=
      ∑i∈ bands F.sector.derivatives h, coalesce P nearSet Y w child i * Call.demand F ζ Y farSet (update w child (P.letter i)) := by
    unfold Prescription.truncated; exact Finset.sum_congr rfl fun i _=>Eq.symm (as_term (spectator F ζ) P hS.laws.toSymmetric F.room.kernel.laws.toSymmetric o r s x y ix iy i hp)
  rw [e]; exact H r x y o hi ζ
end YM.OPE.Flash259HorizonFork
