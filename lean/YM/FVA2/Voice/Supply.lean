import YM.FVA2.Clef.Bach
import YM.FVA2.Clef.Tunes
import YM.FVA2.Voice.Encore
import YM.FVA2.Embr.Provider
import YM.FVA2.Teller.Mass
/-!
# End-to-end supplier (details for `YM/FVA2/Main.lean`)

We can express everything at μ=1 in MS mass convention (`Supplied.mass_unit`),
and at any fixed scale. Log radius when quoting OPE = minus the real argument.
Includes uniqueness of checked N from the generator prescription. Allows also
optional changes within grades. Rotation and stress alignment with
nonperturbative fields and asymptotic error estimates in the physical theory
require additional results.

`ν` in this file is in the logarithmic convention of `YM/MS`. For example use
`ν = Teller.logNu 1` (see `Teller/Mass.lean`) to assert results at unit MS mass.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Voice
open Function Filter Set Finset MeasureTheory Lattice Wilson
open Maxwell Maxwell.Free
open MS MS.Book MS.Book.Convolve MS.Book.Program MS.Plane MS.Koszul MS.Native MS.Wind MS.Rake MS.Theater MS.Menus MS.Tide MS.Fleet MS.Momentum
open MS.Orbit MS.Swirl MS.Swirl.Near MS.High MS.Vista MS.Land
open Arrival Arrival.Episodic Change Slice Press XPos
open PertExtension FormalOPE.RG10 FormalOPE.RG10.MultiGauge Splice
open scoped Classical Topology BigOperators ContDiff
open MS.Dial MS.Rake MS.Vista
open Register Register.WilsonPrescription
open _root_.YM.FVA2.Scale YM.FVA2.Scale.Equator Scale.Facets Scale.Jury Clef
open Generator.Der Generator.Drive
variable {G: Gauge}(N:Register.WilsonPrescription G)(h:G.Simple)
variable (F: Land.MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (M:Prescription ( Press.portDeck G ))
variable (ν:ℝ)
set_option quotPrecheck false
local notation "Y0"=> N.scheme
local notation "C"=> N.criterion
local notation "M1"=> Scale.Measure.adjust Y0 C
local notation "X₀"=> Scale.Measure.start Y0 C
local notation "Xn"=> Scale.Measure.outlook Y0 C
local notation "T'"=> wave ν F
local notation "γ"=> GroupS.ψ C F ν
local notation "E₀"=> GroupS.gaugeN Y0 C F ν
local notation "ℏ₀"=> GroupS.gaugeB C F ν
local notation "γ'"=> GroupS.Ψ C F ν
local notation "F₀"=> GroupS.gaugeM Y0 C F ν
local notation "p"=> ( Scale.Measure.f C ν F )
local notation "Φ"=> Scale.Measure.Z Y0 C ν F
local notation "β"=> Scale.Beta.beta γ
-- Final position-scheme generator laws.
structure Normalized : Prop where
 first : Touched X₀ γ ℏ₀
 criterion : ∀ n t, Instant (fun s=> ℏ₀ s n) ( Clef.weight ( ℏ₀ t n ) + ℏ₀ t n * Reg.Point.stepV (γ t) ( Generator.Drive.engraving ℏ₀ n ) ) t
 weights : ∀ i, Scale.remainder ( M1 i ) ∧ Native ( casting ( M1 i ) β ( Generator.Drive.engraving ℏ₀ i ) )
 unique (T: Frames G): (∀ i, Base (T i) ∧ Scale.remainder (T i)) → (∀ i j (u:i ≤ j), Walk u (T i) (T j)) → (∀ i, Native ( casting ( T i ) β ( Generator.Drive.engraving ℏ₀ i ) )) → T=M1
 check : Slopes Xn γ E₀ ( Generator.Drive.engraving E₀ )
 ms : Slopes T' γ' F₀ ( Generator.Drive.engraving F₀ )
variable (H:Served N F M)
include h H
lemma normative : Normalized N F ν:= by
    obtain hV:= H.toPosted.toQuoted.toContract; obtain hv:= Generator.Drive.clocks_run Y0 C F M h hV ν; exact ⟨ Clef.growsV h hV ν, Clef.evolves ν h hV, fun i=> ⟨ Clef.strict hV ν,Clef.pure_adjusted h hV ν⟩,fun T=> Clef.mark h hV ν T, hv.1,hv.2.1 ⟩
-- See `Optional` in `Clef`: keep the same choice (if using an optional within-grade rotation)
-- for every scale & horizon in the comparisons.
variable (T:Frames G)(ht: O.Score.Civil T)
local notation "ξ"=> Clef.rendition Xn T
local notation "A"=> breeze T γ E₀
open XSpace Normalize
structure Extended : Prop where
 roots : O.Score.Civil (Φ*T)
 application : ∀ d:ℕ, actMark ( (Φ*T) d ) ( couple p ( T' d ) )= ξ d
 recovery (d:ℕ) : Reg.Higher.HasAll XSpace.Cirrus.Front (fun x => Clef.Tunes.orders Y0 C T d x ) ( Clef.Tunes.incurred ν Y0 C F T d )
 smears (d:ℕ) : Orders ( ξ d ) ( Clef.Tunes.incurred ν Y0 C F T d )
 field (t:ℝ) (d:ℕ): Reg.Point.stepV p ( F₀ t d ) * Reg.Point.stepV ( γ t ) ( (Φ*T) d )= ( Φ*T ) d * A t d
 scale : Slopes ξ γ A ( Generator.Drive.engraving A )
 ops : O.Canon.Physical ξ γ A
 produced (n:ℕ)(u:O.Score.Scan G n)(r:ℝ): O.Canon.Gift_shape ( O.Score.seats (Φ*T) ) p u ( fun i=> O.Canon.OPECoefficients T' i r ) ( O.Canon.OPECoefficients ξ u r )
include ht
lemma moving : Extended N F ν T:= by
    obtain hv:=H.toPosted.toQuoted; have hP:=hv.toContract; refine ⟨ Optional.color F ν hP T ht, Optional.operator F ν hP T, Clef.Tunes.exactly ν Y0 C F M T hv, fun _=> Clef.Tunes.proper ν Y0 C F M T hv _, Optional.interconnected F ν hP T ht, Optional.price F h ν hP T ht, Optional.in_fields F h ν hP T ht, fun n u r=> Optional.assists F h ν hP T ht r u ⟩
omit H ht h
local notation "origin"=> Continuum.Continuation.proofStart h ( Reg.supplies Y0 F )
/- user endpoint both paths. Use exact Plot. -/
structure Supplied (k:Bool) : Prop extends Served N F M where
 method : Teller.Homes.Installed Y0 F M true
 maximum : M.team=( origin k ).team
 estimates : Notch.Poise N F M
 normative (v:ℝ) : Normalized N F v
 ope (u:ℝ) : O.Canon.Supplied N F u
 later A' u: O.Score.Civil A' → Extended N F u A'
-- convenience of fixed-scale formulation, at unit MS mass
namespace Supplied
include h
lemma mass_unit {k:Bool} (he:Supplied N h F M k)(n:ℕ): let ν₀:=Teller.logNu 1; let Φ':= Scale.Measure.Z Y0 C ν₀ F; let g:= Scale.Measure.f C ν₀ F; O.Canon.Supplied N F ν₀ ∧ ( (Scale.Beta.beta ( GroupS.Ψ C F ν₀ )).subst g= PowerSeries.derivative ℂ g * Scale.Beta.beta ( GroupS.ψ C F ν₀ ) ) ∧ actMark ( Φ' n ) ( couple g ( wave ν₀ F n ) )= Xn n:= by
    obtain hy:=he.toServed.toPosted.toQuoted.toContract; intro ν₀ Φ' g; exact ⟨ he.ope ν₀,(hy.scales ν₀).dif,hy.series ν₀ n ⟩
end Supplied
include h
/-- End supplier, formal-to-formal conversion in separated physical diagram prescription.
    An estimate for actual physical expectations is a separate input. -/
theorem physical_compare (dial:Bool) : ∃ M:Prescription (Press.portDeck G), Supplied N h F M dial:= by
    obtain ⟨A₀,hA,hT,hS,ht⟩:= Inked.strict_establishment F N h dial; exact ⟨ A₀,hS,hT,hA, Notch.coverage N F A₀ h hS, fun a=> normative N h F _ a hS, ht,fun K v hK=> moving N h F _ v hS K hK ⟩
open XSpace
omit h
-- Complete all choices, even at arbitrary selected Run
lemma provision (h:G.Simple)(L:XSpace.Run)(dial:Bool): ∃ (N:Register.WilsonPrescription G) (F:Land.MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (M:Prescription (Press.portDeck G)), N.run=L∧Supplied N h F M dial:= by
    obtain ⟨N,hN,_⟩:= Register.WilsonPrescription.prepared h L ( XSpace.Initialize.standard G ) 1 one_pos; obtain ⟨F⟩:= MS.Land.bookedMS ( Position.OpenAxis.Plot (Press.portDeck G) ); obtain ⟨M,hS⟩:= physical_compare N h F dial; exact ⟨ N,F,M,hN,hS ⟩
end YM.FVA2.Voice
