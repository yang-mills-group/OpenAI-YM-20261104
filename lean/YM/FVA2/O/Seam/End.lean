import YM.FVA2.O.Seam.Moments
/-!
# FAR projection on actual MS `tour` arrays, chosen inner/OPE data

`Cluster`: two separated groups of points, x at the large exterior scale (exp θ),
y within bounded distance in unit coordinates. Start with the `O/Hue` construction on y
(`recipe`). Need all of `RecipeT`, in particular there's a degree -1 generator V
(for the **exact** projection part of that construction) with its own estimates. There's
still *error* in the resulting projection. Attach arbitrary far spectators; pay for
the separation and projection using prior files in `O/Seam`. `hub` here gives the
estimate on the resulting scalar evaluations at all orders below the budget d. Includes all
output weights through k at the center p(a) = 0.

Use `O/Seam/Loom` and `O/Enh/Sale` to obtain these estimates on the required compact
profile spaces. Not asserting any uniformity in horizon. Spare exponent here (see `Need`)
possibly small; recover the full gap of one from the next level later, see `O/Bind/Stars`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Seam
open MS Function Filter Set Finset MS.Latch Job MS.Plane MeasureTheory Real Metric
open Heat LogTime IntervalFamily Koszul Tone Momentum Landau Fiddle Osc Snap Wire Signal
open Lives MS.City MS.Rake Tune Flux Book Convolve Serve O.Pad Vane High Detect
open MS.Local.Physical MS.Land O.Hue Rough O.Cool O.Clift Rake.Geo O.Price O.Fuse
open scoped Topology ContDiff Interval
variable { G : Gauge }{I W Z A L: Type}{B:Deck G}{K:Booked B}{M:MS_Data G K} {n k d:ℕ}{P:Geo I}{η:I→ℝ}
variable [LinearOrder W][LinearOrder Z][LinearOrder A][LinearOrder L]
variable { x:Position W I }{y:Position Z I}{z:Position A I}{p: Position L I}
variable {R: W→ Label B }{Y:Z→ Label B}{U:A→ Label B}{ Ω:Counter B k → L→Label B }
variable {s:Finset W}{t:Finset Z}{a:L}{φ: W ↪ A}{χ:Z ↪ A}{θ: W ↪ L}
/-- Separate x and y on the large scale. -/
def Cluster (P:Geo I)(x:Position W I)(y:Position Z I): Prop :=
    Mesh (flatten P) y ∧ (∀ i, Cool.Fixed ( y i )) ∧ Mesh P x ∧
        (∀ i, CoverSep P ( x i )) ∧ (∀ i j, CoverSep P ( x i - y j ))
-- combining disjoint lists of positions, with separation
structure Ensemble (x:Position W I)(y:Position Z I)(z:Position A I)
    (R: W→ Label B)(Y:Z→Label B)( U:A→ Label B )(s:Finset W)(t:Finset Z)
    (φ: W ↪ A)(χ:Z ↪ A) :Prop where
    hx: Resembles x R z U φ s
    ht: Resembles y Y z U χ t
    uses : separable z
    distinct i (h:i∈s): φ i∉ map χ t
structure InTune (x:Position W I)(p:Position L I)
    (R:W→ Label B)(Ω:Counter B k→ L→ Label B)(s:Finset W)(θ: W ↪ L)(a:L): Prop where
    sep : separable p
    pos : p a=0
    art i: Ω i a=actor i
    hops(l:Counter B k): Resembles x R p (Ω l) θ s
    fed i (h:i∈s): θ i≠a

structure RecipeT (P:Geo I)(M:MS_Data G K)(X:T ( Glade G I ))
    (k d:ℕ)(r:Details B I k): Prop where
    power: Valid ( Station P ) r
    kind: ∃ V, Response V M P.η (-1) ∧ Reps V 0 (Station P) ∧
        Colorable (Station P) ( X - Physical P.η M r - nav M P.η V ) d k
lemma recipe (h: Mesh ( flatten P ) y)(hp:∀ i,Cool.Fixed ( y i )) :
    ∃ r:Details B I k, RecipeT P M (thicket P M y Y t) k d r := by
    obtain ⟨r,h⟩:= field_whole (M:=M) (R:=Y) h rfl hp
        ( serves ( P:=flatten P ) ( M:=M ) ( r:=Y ) ( mesh_sep h ) ) t d k
    exact ⟨r,h.1,h.2⟩
variable { r: Details B I k }
-- T^(-(n+δ)) (up to the stated factor): large-scale suppression: allow polynomial growth in θ here
abbrev Far_P (P:Geo I)(n:ℕ)(f:I→ℂ): Prop := ∃ C:ℝ,0<C ∧ ∃ k:ℕ,
    ∀ i, ‖f i‖ ≤ C*( habitat P i*(1+P.θ i))^k * Need P n i
lemma hub (hC:Cluster P x y)( h:Ensemble x y z R Y U s t φ χ )
    (hp: InTune x p R Ω s θ a)(hx:RecipeT P M (thicket P M y Y t) k d r):
    let S:= ( map φ s ) ∪ (map χ t)
    let T:= insert a (map θ s)
    let V:= glyph P M z U S
    ∀ i<d, Far_P P (height R s+k) (( V - Fiscal r (fun j=> glyph P M p ( Ω j ) T )) i) := by
    intro S T V
    obtain ⟨hV,hB,hP,ht,hQ⟩:= hC
    obtain ⟨hO,V0,H,hZ,hT⟩:= hx
    obtain ⟨h1,h2,h3,hL⟩:=h
    obtain ⟨hh,ht',he',hr,hv⟩:=hp
    let F:= thicket P M z U S
    let X(i: Counter B k):= thicket P M p ( Ω i ) T
    have hX : Response F M P.η 0:= (firm h3).1
    have hz(i): Certified ( X i ) M P.η 0:= firm hh
    let H1:=FrameZ r X
    have hHH:= Frame_r (p:=r) hz
    let l:=height R s+k
    intro i hi

    -- Estimate from the matching time `amber`, using `final_P`. Includes the
    -- Chaff inputs from lower time ranges.
    have hM:= final_P hP ht H hZ hT hX
        (thicket_gap (s:=s) hP ht hV hB hX ( fun i _ j _=> hQ i j )
            ( fun i=> H_handoff h1 h2 ( mesh_sep hP ) ( mesh_sep hV ) h3 hL ))
        (Frame_v hP ht (fun i=> (hz i).1)
            (fun k i=> single_t (hr k) ( mesh_sep hP ) hh a ht' (he' k) hv ) hO )
        hHH.1 i hi
    have hw : FrameZ r X= H1 := rfl

    -- These surviving scalar evaluations are exactly the ones needed for the OPE.
    rw [ mergeB hX hHH.1 i,
        show Vane.blade ( F i )= V i from congr_fun ( clocked ( R:=U ) ( M:=M ) ( P:=P ) h3 ) i,
        show Vane.blade ( FrameZ r X i )=Fiscal r ( fun j=> glyph P M p ( Ω j ) T ) i from
            congr_fun ( read_F hz (fun i=> clocked hh )) i ] at hM
    obtain ⟨ C,hC,k',hK⟩:= hM
    refine ⟨ C,hC, k',fun j=>?_ ⟩; apply le_trans ( hK j )
    have hZ : (later P ( height R s+k )).dawn.basic j≤ _:=
        (mul_le_mul_of_nonneg_left (add_le_add_right (amber_le P l j) 1)
            (by unfold habitat; positivity : (0:ℝ)≤ habitat P j ))
    gcongr; · exact ((later P l).dawn.basic_pos j).le
    exact hZ

end YM.FVA2.O.Seam
