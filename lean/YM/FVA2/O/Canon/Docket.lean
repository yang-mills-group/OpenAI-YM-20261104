import YM.FVA2.O.Canon.Profiles
/-!
# Canonical OPE arrays from independently specified correlations

`FarCoefficients`: use inner shapes at length one, arbitrary horizon with power-log error
having gap one. `LogPricing`: uses instead the usual OPE specifications on these same shapes
with distances scaled down by r = exp(-t). `Physical` requires both characterizations, with
the exact same family via dilation with the prescribed position arguments, engineering grades,
fields and coupling convention. It includes the proof of the error bound (at each order, pointwise positions
and uniform on fixed compact families of separated shapes), NOT any assertion at diagonal
contacts or of an OPE limit taken simultaneously with a UV limit.

Prove consequences including `kxcoeff` (recover `FarCoefficients` by the profile-
matrix-inverse limit) and `uniqueF`/`unique` for these two
characterizations. `shine` provides `Physical` from the unit characterization
(+ leading Gram setup, scale laws etc.); see `O/{Bind/Stars,Canon/Give}` for supplying
the hypotheses for actual use, on each side of the **formal** Wilson/MS comparison.
No actual-theory OPE estimate here.
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
variable { G:Gauge } { n m k:ℕ }{t r a:ℝ }{ V W:Arenas G }{H:ℝ→Frames G }{ φ:ℝ→Cn }{A:Album G}
variable {f:Fable G n}{ p: FLog G n }{ u:Scan G n }{ P:Geology G k }
/-- FAR characterization (so the default in this definition is irrelevant in the setting of
`Physical`). Fixes UNIT-SHAPE pricing through all perturbative orders and output weights. -/
def FarCoefficients (V:Arenas G) (v:Scan G n) : Fable G n :=
  if h:∃ f, AllC (install V) v f then Classical.choose h else 0
/-- Independently, OPE pricing in the near short-distance convention at separated shapes. -/
def LogPricing (V:Arenas G)(v:Scan G n): FLog G n:=
  if he:∃ p, OPEA (install V) v p then Classical.choose he else 0
-- OPE: actual (power-log) coefficients on physical basis
abbrev OPECoefficients (V:Arenas G)(v:Scan G n): FLog G n:= QuoteP v ( LogPricing V v )
local notation "V0"=> install V
local notation "P'"=> LogPricing
lemma supply_F (f:Fable G n)(h: AllC (install V) u f) : AllC V0 u ( FarCoefficients V u ):= by
  rw [FarCoefficients,dif_pos ( show ∃ f, AllC V0 u f from ⟨f,h⟩ )]; exact Classical.choose_spec _
lemma supply_NE (f:FLog G n)(h:OPEA V0 u f): OPEA V0 u ( LogPricing V u ):= by
  rw [LogPricing,dif_pos ( show ∃ f,OPEA V0 u f from ⟨f,h⟩ )]; exact Classical.choose_spec _
variable { G':ℝ→Frames G }

/-- Requirements on a power-series correlation array to implement its OPE. -/
structure Physical (V:Arenas G)(p:ℝ→Cn)(H:ℝ→ Frames G) : Prop where
    /-- the physical scale law on these arrays -/
    scope : Law V p H
    awake : Observed ( install V )
    wardRank : Ground V
    dimensions : Regular V
    far {n:ℕ} u : AllC (install V) (n:=n) u (FarCoefficients V u)
    dilation {n:ℕ} u : LogPricing V (n:=n) u =
        ledger p ( Night H ) ( Astro H ) ( Club ( FarCoefficients V ) ) u
    works {n:ℕ} u : OPEA ( install V ) ( n:=n ) u ( LogPricing V u )
namespace Physical
variable (h:Law V φ H)(hp:Observed (install V))(he:Ground V)( ht:Regular V )
lemma listed (h:Physical V φ H):
    ∀ s:Set (Points n), IsCompact s→ s⊆conf n→ ∀ (k i:ℕ)(u:Scan G n),
        Exteriors ( install V ) s ( LogPricing V u ) u k 1 i :=
    fun _ hv hz _ _ u=> ( h.works u ).through _ hv hz _ _
include h hp he ht
theorem shine ( hF:∀ {n:ℕ}(u: Scan G n),∃ F,AllC ( install V ) u F ): Physical V φ H := by
    have H0 {n:ℕ}(u:Scan G n): AllC V0 u ( FarCoefficients V u ) :=
        supply_F _ (Classical.choose_spec (hF u))
    have hv {n:ℕ}(u:Scan G n):
        OPEA V0 u ( ledger φ ( Night H ) ( Astro H ) ( Club ( FarCoefficients V )) u ) :=
        shines h ht ( fun p=> H0 p )
    have hu {n:ℕ}(u:Scan G n) : OPEA V0 u ( LogPricing V u ):= supply_NE _ ( hv u )
    exact ⟨ h,hp,he,ht,H0, fun u=> Project.settle he ht ( hu u ) ( hv u ), hu ⟩
omit h hp he ht
variable (hR:Physical V φ H)
include hR
-- static consequences
lemma unique (u:Scan G n){p:FLog G n}(h:OPEA ( install V ) u p): LogPricing V u=p :=
    Project.settle hR.wardRank hR.dimensions ( hR.works u ) h
lemma uniqueF (u:Scan G n){p:Fable G n}(h:AllC ( install V ) u p): FarCoefficients V u=p :=
    Bind.independent hR.scope hR.wardRank hR.dimensions hR.awake ( hR.far u ) h
-- canonical consistency across geometry and log at this fixed setup
lemma start (u:Scan G n): LogPricing V u 0= FarCoefficients V u:= by rw [ hR.dilation,first_t hR.scope ]
lemma start_u (u:Scan G n): OPECoefficients V u 0= FarCoefficients V u:= by rw [ OPECoefficients,zero_t,hR.start ]
lemma shapes (t:ℝ)(x:Points n)(hp:x∈conf n):
    OPECoefficients V u t x = FarCoefficients V u ( squeeze t x ) := by
    rw [ OPECoefficients, onward hR.wardRank hR.dimensions ( hR.works u ) hp, hR.start ]

-- Rank of the free Gram on an actual choice of test P. And FAR readout, e.g. with this choice.
lemma light (d:ℕ): ∃ P: Geology G d, H_pos ( Portfolio (install V) P ) ∧ Detected V P:= by
    obtain ⟨P,hP⟩:= reserve hR.wardRank hR.dimensions hR.awake d
    exact ⟨P,hP,positive_unit hP⟩
theorem kxcoeff (P: Geology G k)(ht:Detected V P)
    (u:Scan G n)(t:Test n)(b:Toon G k)(i:ℕ) :
    Tendsto (fun s=> coeff i ( FProg H (install V) P u s t b )) atTop
        (𝓝 ( coeff i ( Yield t ( FarCoefficients V u ) ( Dframe.flash b ) ) )) :=
    Read.limit_κ hR.scope hR.dimensions hR.awake ht ( hR.far u ) t b i

end Physical
end YM.FVA2.O.Canon
