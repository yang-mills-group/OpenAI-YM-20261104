import YM.Integration.WilsonPhysicalStationMixedWickNorms
import YM.Integration.WilsonPhysicalStationMixedWickChamber
import YM.Integration.WilsonPhysicalStationMixedWickMetered

/-! Original before-radius procurement of the positive weighted lower-frame inverse. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickSolvent
open Filter Finset Function Lattice RG Wilson Labels Source Cells Extraction Table Climb Trace
open PhysMS Spec OPE Next.UVStress Trace.Pilot PhysicalNext.Repeat.Legato
open GapsContact OPE.Levy Stamps Seams Ascent Trace MergeProof.East Maxwell XSpace XSpace.Normalize
open Trace.Terrace Trace.Over FVA2 FVA2.Register WilsonThermometerUnitFilingFourSquare Next.Rank.Station
open MS MS.Land MS.Menus MS.Theater XSpace.Structure1
open Local.Physical
open WilsonPhysicalStationMixedWickNamedGram (amount electrode)
open WilsonMovingForkReporterBothArms (Filed)
open WilsonPhysicalStationGradedLowerPanel (metered frame)
open WilsonMeasuredPublicEntranceNativeLowerFrame (panel)
open WilsonPhysicalStationMixedBasisSale (Sold)
open scoped BigOperators Classical Topology Matrix.Norms.Operator
open WilsonPhysicalStationGradedLowerPanel (charge cross right)
open WilsonPhysicalStationLowerReceiver (ear)
open WilsonPhysicalStationMixedWickMetered (total)
open WilsonPositionProgramPublicWickGram (nodes reading)
variable {G:Gauge}(R:Run G){S:Table R.family.book}(B:Deck G)(e:ℕ)(a:Axis)
local notation "I" => Glyph B e

structure Room where
  site:Set (Points 2)
  compact:IsCompact site
  clear:site⊆conf 2
  ξ:Points 2
  generic:ξ∈YM.generic 2
  neighborhood:site∈𝓝 ξ
  rank:∀y∈site,IsUnit (panel R B e a y).det
  floor:ℕ
  cost:ℝ
  positive:0<cost
  solvent:∀(U:tower S)(x y:Points 2),y∈site→∀(T:ℝ),0<T→∀D:ℕ,floor≤D→
    ‖metered B e T (frame R U B e a x)-panel R B e a y‖≤total R B e a site compact clear/((D:ℝ)+1)→
    IsUnit (metered B e T (frame R U B e a x)).det ∧ ∀(Q:ℕ)(L:S.Field e→ₗ[ℂ]ℂ),
      (∑j:I,charge R U B e a x T Q L j • ear R (e:=e) x (right R U B e j)=L) ∧
      ∀j:I,‖charge R U B e a x T Q L j‖*T^Q≤T^j.2.1.val*cost*‖cross R U B e a T Q L‖

theorem original :Nonempty (Room R (S:=S) B e a):=by
  obtain ⟨δ,C,dp,cp,admit⟩:=WilsonPhysicalStationMixedWickInverse.original R (S:=S) B e a
  obtain ⟨u,ρ,_,rp,inverse⟩:=WilsonOriginalPublicRelativeGramReference.original a (id:I→I) Function.injective_id
  let τ:=min δ ρ
  have safe:0<τ:=lt_min dp rp
  obtain ⟨K,compact,clear,ξ,hξ,inside,small⟩:=WilsonPhysicalStationMixedWickChamber.original R B e a
    (τ/2) (half_pos safe)
  let bill:=total R B e a K compact clear
  obtain ⟨floor,hfloor⟩:=exists_nat_ge (bill/(τ/2))
  have rank (y:Points 2)(hit:y∈K):IsUnit (panel R B e a y).det:=
    (inverse _ ((small y hit).trans ((show τ/2≤τ by linarith only [safe]).trans (min_le_right δ ρ)))).1
  refine ⟨⟨K,compact,clear,ξ,hξ,inside,rank,floor,C,cp,?_⟩⟩
  intro U x y member T tp D late paid
  have age:(floor:ℝ)≤D:=by exact_mod_cast late
  have available:bill/((D:ℝ)+1)≤τ/2:=by
    apply (div_le_iff₀ (by positivity)).mpr
    have fund:=((div_le_iff₀ (half_pos safe)).mp (hfloor.trans age))
    nlinarith only [fund,safe]
  let H:=metered B e T (frame R U B e a x)
  let G₀:=panel R B e a y
  have entries:‖(fun i j:I=>H i j)-(fun i j:I=>G₀ i j)‖≤τ/2:=
    (WilsonPhysicalStationMixedWickNorms.original (H-G₀)).trans (paid.trans available)
  have near:‖(fun i j:I=>H i j)-reading a (nodes a) (id:I→I)‖≤τ:=by
    have estimate:=dist_triangle (fun i j:I=>H i j) (fun i j:I=>G₀ i j)
      (reading a (nodes a) (id:I→I))
    simp only [dist_eq_norm] at estimate
    have second:‖(fun i j:I=>G₀ i j)-reading a (nodes a) (id:I→I)‖≤τ/2:=
      small y member
    linarith only [estimate,entries,second]
  exact ⟨(inverse H (near.trans (min_le_right δ ρ))).1,admit U x T tp (near.trans (min_le_left δ ρ))⟩

end YM.Integration.WilsonPhysicalStationMixedWickSolvent
end
