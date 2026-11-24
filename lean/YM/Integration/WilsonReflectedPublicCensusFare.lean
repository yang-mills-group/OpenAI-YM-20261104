import YM.Integration.WilsonReflectedPublicChargedRoster
import YM.Integration.WilsonReflectedPublicOpticalColumns
import YM.Integration.WilsonReflectedStationPrefix
/-! Physical cutoff costs for the same finite portfolio of public reflected
columns at a reporting mesh finer than both of its genuine birth stations. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedPublicCensusFare
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato Work.G08 Next.Rank Marker MergeProof Accent Extra.Multi
open RG05Readout RG05Readout.Address RG05Readout.Records Menu Extra.Trajectories Push.GridApprox.Nil
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetCylinder WilsonThermometerOffsetResidue
open WilsonThermometerOwnOffsetField WilsonThermometerMarchSource WilsonAddressedAlignedColumn
open WilsonAddressedPublicPool WilsonAddressedPublicCrown WilsonThermometerReflectedTrajectory
open scoped Classical Topology BigOperators
open WilsonReflectedPublicOrientedFaces
open Climb Maxwell Maxwell.Free MS.Land Next.Rank.Station MergeProof.East Next.UVStress Trace.Terrace Trace.Pilot GapsContact GapsContact.Seams
open GapsContact.Stamps Trace GapsContact.Ascent
open WilsonMeasuredPublicBank WilsonPositionProgramPublicStations WilsonReflectedPublicStationFare
variable {G:Gauge} {R:Run G} {order:Extraction.Order} {S:Table R.family.book} (F:Final R.family order S)
  {l:Ultrafilter (ℕ×ℕ)} {H:(Bel R.family.book).Hierarchy}
local notation "C₀" => R.family
local notation "mesh" => R.family.S.a

theorem move (R:Run G) {d j f N p:ℕ} (Y:R.family.label d) (income:ℝ)
    (ref:R.family.ref d≤j) (before:j≤f) (live:f≤N)
    (budget:quota R.family d j N p Y≤R.family.S.a j^d*income) :
    max 1 (2*(R.family.S.a f^d)⁻¹*quota R.family d f N p Y) ≤
      max 1 (2*(R.family.S.a j/R.family.S.a f)^(d+1)*income) := by
  apply max_le_max_left
  have bound := WilsonReflectedStationPrefix.quota R (p:=p) ref before live Y
  have full := bound.trans (mul_le_mul_of_nonneg_left budget
    (div_nonneg (R.family.S.a_pos _).le (R.family.S.a_pos _).le))
  calc
    _ ≤ 2*(R.family.S.a f^d)⁻¹*((R.family.S.a j/R.family.S.a f)*(R.family.S.a j^d*income)) :=
      mul_le_mul_of_nonneg_left full (mul_nonneg zero_le_two (inv_nonneg.mpr (pow_pos (R.family.S.a_pos f) d).le))
    _ = _ := by rw [pow_succ,div_pow];ring

variable {D d k:ℕ}{r s B:ℝ}{stock:Bank F l D s B}{cap:d≤D}{W:Vane R.family k}
  {fits:D≤k}{U:Spin.change S d}

theorem original (P:Pair F stock cap W fits U r)(checked:W.checked order H k)
    (weak:Bool)(v:S.Field d){f N p:ℕ}(past:station F P weak≤f)(deep:f<N) :
    let Y:=(P.arm weak v).source (N,p)
    max 1 (2*(mesh f^d)⁻¹*quota C₀ d f N p Y) ≤
      max 1 (2*(mesh (station F P weak)/mesh f)^(d+1)*fee F P weak v) := by
  obtain ⟨ref,paid⟩:=WilsonReflectedPublicStationFare.original F P checked weak v
  exact move R ((P.arm weak v).source (N,p)) (fee F P weak v) ref past deep.le
    (paid N p (past.trans_lt deep))

end YM.Integration.WilsonReflectedPublicCensusFare
end
