import YM.FVA2.DerivD.Past
import YM.FVA2.DerivD.Perspective
import YM.FVA2.DerivD.Exact
import YM.FVA2.Clef.Tunes
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.DerivD
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick Metric Real TopologicalSpace
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical Matrix ComplexOrder
open FVA2.Scale MS.Rake MS.Theater Level O.Score LogTime MS.Plane MS.Heat MS.Tone Momentum Rake.Geo
open Equator Facets Dframe O.Enh O.Bind O.Project
/-!
# Optional upgrade to smooth coefficient estimates

Both sides of the same formal Wilson/MS comparison. Includes bounds on
derivatives of the error `Submit` (NEAR results), and also of the coefficients
themselves. No extra differentiability hypotheses. First-gradient physical field
recurrence with constant coefficients in the normalization chosen here. Builds
on `O/Canon`; use as potential supplier for actual-to-formal upgrade tasks too.
Costs and parameter order as explicit in this file; no estimate of derivatives
of the cutoff-removal error in approximating these objects.
-/
open O.Canon O.Read
open XSpace Register Register.WilsonPrescription
variable {G: Gauge}{U: Arenas G}{p:Staff G}{H:ℝ→Frames G}{r:ℝ→Cn}
structure Elaborate (U:Arenas G)(p:Staff G)(r:ℝ→Cn)(H:ℝ→Frames G): Prop where
    books : Physical U r H
    parameter : Influence p (install U)
    coefficients {n:ℕ} (x:Points n) : x ∈ conf n → ∀ (t:ℝ)(u:Scan G n)(k:ℕ)(b:Q G),
        ContDiffAt ℝ ∞ ( fun q:Points n×ℝ=> coeff k (OPECoefficients U u q.2 q.1 b )) (x,t)
    theme { n:ℕ } (t:ℝ)(u: Scan G n)(k:ℕ)(b:Q G) (x:Points n) : x∈ conf n →
        ContDiffAt ℝ ∞ (fun t:Points n×ℝ=> coeff k (LogPricing U u t.2 t.1 b)) (x,t)
    atAll {n:ℕ} (b:Q G)(x:Points n) : x ∈ conf n →
        Shard p (fun x (u:Scan G n)=> FarCoefficients U u x b) x
    estimate { n m :ℕ } (d:ℕ)(s:Set (Points n))(K:Set (Points m)) :
        IsCompact s → s ⊆ conf n → IsCompact K → K ⊆ Outside m →
        ∀ (u:Scan G n)(v:Scan G m)(i j:ℕ), Rain ((d:ℝ)+1-( totalG u:ℝ )) ( fun (x:↥( s ×ˢ K )) t=>
            iteratedFDeriv ℝ j ( fun y:Points n × Points m=>
                coeff i ( Submit (install U) u v t ( LogPricing U u ) d y.1 y.2 ) ) x.val )
    pace {n:ℕ} (s:Set (Points n)) : IsCompact s → s ⊆ conf n →
        ∀ (b:Q G)(v:Scan G n)(i j:ℕ), Rain (( heft b:ℝ )-( totalG v:ℝ )) ( fun (x:↥s) t=>
            iteratedFDeriv ℝ j ( fun x'=> coeff i ( OPECoefficients U v t x' b ) ) x.val )
lemma elaborates (hQ:Physical U r H)(h:Influence p (install U)): Elaborate U p r H :=
  ⟨hQ, h, fun _ hP _ _ _ _=> goes_tag hQ h hP _ _ _ _,
    fun _ _ _ _ _ hp=> line_t hQ h hp _ _ _ _, fun _ _ h'=> establish hQ h' h _,
    fun d _ _ hs h' hK he u v i j=> slip hQ h hs h' hK he d (u,v,i) j,
    fun _ hs ht _ _ _ _=> costs h hQ hs ht _ _ _ _ ⟩

variable (N: Register.WilsonPrescription G)(M:MS_Data G ( Position.OpenAxis.Plot ( Press.portDeck G ) ))
variable (S:MS.Land.Prescription ( Press.portDeck G ))(Y:Frames G) (a:ℝ)
local notation "F"=> Register.WilsonPrescription.scheme N
local notation "K"=> Register.WilsonPrescription.criterion N
local notation "T"=> FVA2.Scale.Measure.f K a M
local notation "X"=> Measure.outlook F K
local notation "Ψ"=> Equator.wave a M
local notation "Z"=> Measure.Z F K a M
local notation "Γm"=> GroupS.gaugeM F K M a
local notation "Γ"=> GroupS.gaugeN F K M a
local notation "r"=> GroupS.ψ K M a
local notation "ρ"=> GroupS.Ψ K M a
-- in pact of main supplier
local notation "Ξ"=> authority a M
def exchangeP : Staff G:= altered ( seats Z ) ( seats ( replay Z ) ) ( reprice T Ξ )
variable {S N M}
variable (hp:System.Contract N.scheme N.criterion M S)
include hp
lemma glory_M : Elaborate Ψ Ξ ρ Γm:= elaborates ( before_M hp a ) ( DerivD.inspiration a M )
lemma glory_X : Elaborate X ( exchangeP N M a ) r Γ:= by
    apply elaborates ( after_W hp a ); unfold exchangeP; rw [ ← invested ( ν:=a ) hp ]; exact billH ( DerivD.inspiration a M ) ( spin_k ( office hp )) ( hp.cpl a |>.start )
-- including optional within-grade adjustments
lemma embellished (h:G.Simple)(hY: Civil Y) : Elaborate ( Clef.rendition X Y ) ( altered (seats Y) (seats (replay Y)) ( exchangeP N M a ) ) r ( Clef.breeze Y r Γ ):= by
    obtain H:= glory_X a hp; apply elaborates ( Clef.Optional.in_fields M h a hp Y hY ); rw [show install ( Clef.rendition X Y )=marking ( seats Y ) (install X) from (unveil H.books.dimensions hY).symm]; exact markV H.parameter ( spin_k hY )
end YM.FVA2.DerivD
