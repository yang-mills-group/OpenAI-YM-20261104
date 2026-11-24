import YM.Integration.WilsonMaxwellThermometerReflectedEntered
/-! The measured signed coordinates are fixed on their physical star. Use these
same numbers on one independent inversion, down to its enrolled older report. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerReflectedEnteredPhysical
open Function Filter Set Finset Lattice Wilson Labels RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Embroider Source Source.Drops
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard
open Table Spec Extraction OPE OPE.Orbits Climb Trace Trace.Pilot Next.UVStress
open RG17 PhysMS PhysMS.Frame Maxwell Maxwell.Free XSpace XSpace.Normalize
open WilsonPositionCapTransport (Book)
open WilsonPositionThermometerCapStation (Group)
open WilsonPositionCorrectedCap (adjusted)
open WilsonMarkedIndependentNormalizedElection (deck)
open WilsonMaxwellThermometerReflectedPhysicalColumns (levels)
open WilsonMaxwellThermometerReflectedStation (Name source)
open WilsonMaxwellThermometerReflectedEntered (current)
open scoped Topology Classical BigOperators
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{T:Table R.family.book}
variable (F:Final R.family f T)(P:ℝ→tower T)(V:Store G)
variable {H:(Bel R.family.book).Hierarchy}{l:Ultrafilter (ℕ×ℕ)}(A:ℝ→Group R.family 6)
variable (a:Axis)(b:Sec G 6)(d:Fin 2→ℕ)(fit:∀i,levels i<d i)
variable {D k u e:ℕ}
local notation "Q" => deck (G:=G) levels d fit

theorem original (simple:G.Simple)(book:Book (f:=f) (l:=l) (H:=H) A P)(lead:Leading F P)
    (paid:WilsonPositionProgramNominatedMenuInvoice.issued G R.kit)
    (big:0<D)(rails:Rails 0 k u e)(he:1 ≤ e)(cap:capP Q ≤ k):
    ∃floor:ℕ,∀ᶠ r in trail,let Z:=adjusted F P V A r
    ∀(U:XSpace.Run){stage:ℕ}(B:WilsonPositionProgramReporterBand.Band R U stage)
      (φ:Wilt Q)(w:Fin 2→ℝ),(∀ᶠ z:ℝ in atTop,Bough Q φ 1 z w) →
    ∃C:ℝ,0 ≤ C ∧ ∃p:ℕ,∀ᶠ t:ℕ in atTop,let m:=B.reporter+t
      ∀N per:ℕ,Z.station.k<N → ∀v₀:ℕ,floor ≤ v₀ → B.lower t ≤ v₀ → v₀ ≤ m →
      ∀M:ℕ,m ≤ M → ∀s:Bool,
        ‖current R d fit big φ (fun n=>source R d fit Z a b Z.station.k n N per) m v₀ M k s‖
          ≤ C*(1+(B.index t:ℝ))^p:=by
  obtain ⟨floor,program⟩:=WilsonMaxwellThermometerReflectedEntered.original R d fit simple
    (WilsonPositionProgramNominatedMenuInvoice.wallet G) paid.2 big rails he cap
  obtain ⟨E,_,fare⟩:=WilsonMaxwellThermometerReflectedUniformFare.original F P V A a b d fit
    simple book lead e 1 zero_lt_one
  refine ⟨floor,?_⟩
  filter_upwards [fare] with r entitled
  intro Z U stage B φ w profile
  let income:=E*(R.family.path.levels.clock.hatBeta Z.station.k)^((1:ℝ))
  obtain ⟨C,hC,p,late⟩:=program U B φ w profile |income| (abs_nonneg _)
  refine ⟨C,hC,p,?_⟩
  filter_upwards [late] with t price
  intro m N per strict v₀ active low up M cutoff s
  exact price v₀ active low up M cutoff _ (fun n i=>(entitled N per strict n i).trans (le_abs_self income)) s

end YM.Integration.WilsonMaxwellThermometerReflectedEnteredPhysical
