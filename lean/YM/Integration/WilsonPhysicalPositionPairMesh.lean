import YM.Integration.WilsonPhysicalTwoHomeOpticalCash
import YM.Integration.WilsonOriginalTwoFlatPublicMixedMesh
import YM.Integration.WilsonMovingForkOpticalBook

/-! The genuine common reporter on two bounded-ratio weak books uses the
inner length for its mesh, even when their enrolled dates differ. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalPositionPairMesh
open Filter Function Set Finset Lattice RG Wilson Cells Extraction Spec Table PhysicalNext.Repeat.Legato Climb
open PhysMS Trace.Pilot OPE OPE.Therm
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonMovingForkOpticalBook (reporter)
open WilsonThermometerUnitFilingFourPoolClock (outer)
open scoped Classical BigOperators Topology
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
  {ℓ:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{arch:Trace.Terrace.Arch R.family}
    {D T:ℕ}{δ:ℝ}(books:(s:{s:ℝ//0<s ∧ s<δ})→Book F (l:=ℓ) H arch D T s.val)

def two {α:Type*}(inner outer:α)(i:Fin 2):α:=if i=0 then outer else inner

theorem original (simple:G.Simple)(bliss:Bliss F ℓ arch H)(slow:WilsonWindowReportingPace.Slow R.kit)(k:Fin (D+1)):
  ∀ᶠσ in trail,∀inner outer:{s:ℝ//0<s ∧ s<δ},inner.val=σ→σ ≤ outer.val→ outer.val ≤ 2*σ→
    R.family.S.a (reporter F books (two inner outer))/σ ≤ (wilson arch σ)^2:=by
  classical
  have school:=WilsonOriginalTwoFlatPublicMixedMesh.original F simple bliss slow D T 1 (fun _:Fin 2=>k) books
  filter_upwards [school,WilsonPhysicalTwoHomeOpticalCash.room F simple bliss] with σ mesh reach
  intro inner outer home lower upper
  apply (mesh (two inner outer) ?_ ?_).1
  · intro i
    by_cases e:i=0
    · exact ⟨by simpa [two,e] using lower,by simpa [two,e] using upper.trans reach.2⟩
    · simp only [two,e,if_false,home,le_refl,true_and]
      exact (lower.trans upper).trans reach.2
  · exact ⟨1,by simpa [two] using home⟩

end YM.Integration.WilsonPhysicalPositionPairMesh
end
