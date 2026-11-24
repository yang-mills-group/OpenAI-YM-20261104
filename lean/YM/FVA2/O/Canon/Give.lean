import YM.FVA2.O.Canon.Docket
import YM.FVA2.Parity.Kit
/-!
# Supply physical OPE conversion and comparison **on the formal Wilson contract**

Construct `Physical` on BOTH of these formal continuum arrays. The `Contract` is supplied
(not an assumption of the final theorem), incorporating the independent position-scheme solution
with mass-independent adjustment. `OPECoefficients` on each side are characterized independently
just using that side's correlations; the `opeeq` field gives their equality using the same conversion as
in the correlations. Frame matrices in input-first index convention in `Gift`.

`ν` in this file is in the logarithmic convention of `YM/MS`. For example use
`ν = Teller.logNu 1` (see `Teller/Mass.lean`) to assert results at unit MS mass.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Canon
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick Metric Real TopologicalSpace
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical Matrix ComplexOrder
open FVA2.Scale MS.Rake MS.Theater Level O.Score LogTime MS.Plane MS.Heat MS.Tone Momentum Rake.Geo
open Equator Facets Dframe O.Enh O.Bind O.Project O.Read
open Register Register.WilsonPrescription
variable { G:Gauge }{ n m k:ℕ }{t ν:ℝ}
variable { V W:Arenas G }{Y:Initialize G}{X:Normalize.Store G}{K:Rose.Pick X}
variable {T:Land.MS_Data G ( Position.OpenAxis.Plot ( Press.portDeck G ) )}
variable {M:Prescription ( Press.portDeck G )}{u:Scan G n}{ p:Cn }{P: Geology G k}
local notation "f"=> Scale.Measure.f K ν T
local notation "Z"=> Scale.Measure.Z Y K ν T
local notation "AI"=> Scale.Measure.outlook Y K
local notation "M0"=> wave ν T
local notation "ξ"=> seats Z
local notation "ψ"=> FVA2.Scale.GroupS.ψ K T ν
local notation "Ψ"=> FVA2.Scale.GroupS.Ψ K T ν
local notation "B1"=> FVA2.Scale.GroupS.gaugeN Y K T ν
local notation "B0"=> FVA2.Scale.GroupS.gaugeM Y K T ν
variable (h: System.Contract Y K T M)
include h

lemma before_M (ν:ℝ):
    Physical (wave ν T) (FVA2.Scale.GroupS.Ψ K T ν) (FVA2.Scale.GroupS.gaugeM Y K T ν) :=
  Physical.shine ( h.scales ν |>.minimal ) (seenMS ν T) ( fun _=> Equator.before ν T )
    (regular_wave ν T) (fun _=>⟨_, Bind.FAR ( ( h.scales ν ).minimal )⟩)
lemma office : Civil (Measure.Z Y K ν T) :=
  ⟨fun i=> (h.joint ν i).1, fun i=> (h.joint ν i).2.1, fun p=> (h.sees p ν).1⟩
lemma invested : ExchangeA f ξ (install M0) = install AI := by
  rw [ExchangeA, tune_live ( h.cpl ν |>.start ), unveil ( tune_reg ( regular_wave ν T ) ) ( office h ),
    show Mark Z ( TuneQ f M0 )=AI from funext ( h.series ν )]
lemma after_W (ν:ℝ):
    Physical (Measure.outlook Y K) (FVA2.Scale.GroupS.ψ K T ν) (FVA2.Scale.GroupS.gaugeN Y K T ν) := by
    let f' := Measure.f K ν T
    let Z' := seats (Measure.Z Y K ν T)
    obtain hp := before_M h ν
    have he : Ground ( Measure.outlook Y K ) := by
        intro i; rw [← h.series ν]
        exact step_mark _ _ ( ( h.joint ν _ ).1 ) ( step_dawn _ _ (Equator.before ν T) )
    obtain hx := (observing (A:=install ( wave ν T )) ( T:=Z' ) ( h.cpl ν |>.start ) hp.awake)
    change Observed (ExchangeA ( Measure.f K ν T ) ( seats ( Measure.Z Y K ν T ) ) _) at hx
    rw [invested h] at hx
    apply Physical.shine ( h.scales ν |>.check ) hx he ( fun _ _ p=>(h.sees p ν).2 )
    intro n i
    refine ⟨funds ( Scale.Measure.f K ν T ) ( seats ( Measure.Z Y K ν T ) )
        ( seats ( replay ( Measure.Z Y K ν T ) ) ) ( FarCoefficients (wave ν T) ) i,?_⟩
    rw [← invested (ν:=ν) h]
    exact funds_good ( h.cpl ν |>.start ) ( spin_k ( office h )) hp.far

-- OPE transformation theorem
lemma property_work (ν:ℝ)(u:Scan G n):
    LogPricing AI u =
      holding (Scale.Measure.f K ν T) (seats (Scale.Measure.Z Y K ν T))
        ( seats ( replay ( Scale.Measure.Z Y K ν T ) ) ) ( LogPricing ( wave ν T ) ) u := by
    apply Physical.unique (after_W h ν)
    rw [ ← invested h ( ν:=ν ) ]; exact paid_w ( h.cpl ν |>.start ) ( spin_k ( office h ) ) ( before_M h ν |>.works )

lemma work_v (t:ℝ) :
    Gift_shape ξ f u (fun v=> LogPricing M0 v t) (LogPricing AI u t) := fun i=> by
  rw [property_work h ν u]; exact rate (spin_k (office h))
lemma opeeq (t:ℝ) :
    Gift_shape ξ f u (fun v=> OPECoefficients M0 v t) (OPECoefficients AI u t) := fun i=>
  Gift.total (( h.cpl ν ).start) (work_v (u:=u) (ν:=ν) h t i)
lemma tested (t:ℝ)(v:Test n) :
    Gift ξ f u (fun w=> Yield v ( OPECoefficients M0 w t )) ( Yield v ( OPECoefficients AI u t ) ) :=
  mentions v (opeeq h t) ( price_rolling t ( ( ( after_W h ν ).works u ).toMarkup ) u )
    ( fun v=> price_rolling t ( ( ( before_M h ν ).works v ).toMarkup ) v ) ( ( h.cpl ν ).start )
omit h
variable (N:Register.WilsonPrescription G)

/-- Both independent OPE characterizations valid, with the `Measure.f` and `Measure.Z`
coefficient identity (use `r` as the argument of `LogPricing`, i.e. logarithmic). -/
structure Supplied (N:Register.WilsonPrescription G)
    (T: MS_Data G ( Position.OpenAxis.Plot ( Press.portDeck G ) )) (ν:ℝ) : Prop where
    continuum : Physical (wave ν T) (GroupS.Ψ N.criterion T ν)
                    (GroupS.gaugeM N.scheme N.criterion T ν)
    wilson : Physical (Measure.outlook N.scheme N.criterion) (GroupS.ψ N.criterion T ν)
                    (GroupS.gaugeN N.scheme N.criterion T ν)
    gifts {n:ℕ} (u:Scan G n) (r:ℝ) : Gift_shape
        (seats (Measure.Z N.scheme N.criterion ν T)) (Measure.f N.criterion ν T)
        u ( fun v=> OPECoefficients (wave ν T) v r )
        ( OPECoefficients ( Measure.outlook N.scheme N.criterion ) u r )
    albums : install (Measure.outlook N.scheme N.criterion) =
                ExchangeA (Measure.f N.criterion ν T) ( seats ( Measure.Z N.scheme N.criterion ν T ) )
                    ( install ( wave ν T ) )
theorem provides (h: System.Contract N.scheme N.criterion T M) (ν:ℝ): Supplied N T ν :=
    ⟨before_M h ν, after_W h ν, fun _ r=> opeeq h r, (invested h).symm⟩
/-- End-to-end supplier including the formal OPE. -/
theorem identified (g:G.Simple)
    (T: MS_Data G ( Position.OpenAxis.Plot (Press.portDeck G) )) (dial:Bool):
    ∃ M: Land.Prescription ( Press.portDeck G ),
        M.team=(Continuum.Continuation.proofStart g (Reg.supplies N.scheme T) dial).team ∧
            Register.WilsonPrescription.Served N T M ∧ ∀ ν, Supplied N T ν := by
  obtain ⟨M,hM,H⟩ := N.serves g T dial
  exact ⟨M,hM,H, provides N H.toPosted.toQuoted.toContract⟩

end YM.FVA2.O.Canon
