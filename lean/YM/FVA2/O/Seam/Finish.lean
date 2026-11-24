import YM.FVA2.O.Seam.Foyer
/-!
# Prove the FAR approximation after attaching spectators and projecting

`final_P`: take the full left and projected (`FrameZ`) sets of insertions. Need the
hypotheses above `holdF`, incl. *before* attachment, approximation by physical plus exact
(`Colorable` error), and two `Chaff` estimates (smalls on the whole range t ≤ θ).
Match at the intermediate time `amber`. Show that the remainder at matching is suppressed
in our rough norm, **after removing the exact part** -- attach the spectator product to
a primitive for that part and use an IVP to extend it from this matching time. Carry
estimate to the scalar readout using `inclusive`. Exact part really disappears exactly
there, by `closeQ`. See `O/Seam/End` to fit these hypotheses. No estimate on actual
nonperturbative OPE involved.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Seam
open MS Function Filter Set Finset MS.Latch Job MS.Plane MeasureTheory Real Metric
open Heat LogTime IntervalFamily Koszul Tone Momentum Landau Fiddle Osc Snap Wire Signal
open Lives MS.City MS.Rake Tune Flux Book Convolve Serve O.Pad Vane High Detect
open MS.Local.Physical MS.Land O.Hue Rough O.Cool O.Clift Rake.Geo O.Price O.Fuse Knot
open scoped Topology ContDiff Interval
variable { G:Gauge } { I W Z : Type } {B:Deck G}{K:Booked B}{M:MS_Data G K}{P:Geo I}
variable {n k d m:ℕ}{v:ℤ}{i:I}
variable {T':I→ℝ}{H V F X : T ( Glade G I )}{Ω: Counter B k→ T ( Glade G I )}{p:Details B I k}
lemma seat_t (h:∀ n,seatB T' (H n)=seatB T' (V n)): peek H i ( T' i )= peek V i ( T' i ):= funext fun n=> congr_fun ( congr_fun ( h n ) i ) 0 -- i
lemma send_E (h:∀ i,seatB ( amber P n ) (F i)= seatB ( amber P n ) ( X i )): sendT ( Beg P n ) (nav M P.η F k)=sendT ( Beg P n ) (nav M P.η X k):= by
    funext i; change peek _ i (amber P n i) k= peek _ i (amber P n i) k; rw [steers,steers,seat_t h]
lemma mergeB (hv:Response F M P.η v)(hx:Response X M P.η v)(n:ℕ): blade (( F-X ) n )= blade (F n)-blade (X n):= blade_minus (fun i=> total_peak hv i n) (fun i=> total_peak hx i n) (fun i=> total_peak ( hv.sub hx ) i n)
variable [LinearOrder W]{ x:Position W I}{R: W→Label B} {s:Finset W}
variable (hp:Mesh P x)(ht:∀ i,CoverSep P ( x i )) (he:Response V M P.η (-1)) (hk:Reps V 0 (Station P))
    (h:Colorable (Station P) (X-Physical P.η M p-nav M P.η V) d k)
variable (hu:Response F M P.η 0) (hF: Chaff ( deckB P ) P ( F-rootT P M x R s X ))
    (hX: Chaff ( deckB P ) P ( FrameZ p Ω-rootT P M x R s ( Physical P.η M p ) ))
local notation "Qx"=> rootT P M x R s
local notation "Y"=> FrameZ p Ω
local notation "A"=> nav M P.η V
local notation "U"=> Beg P ( height R s + k )
local notation "Ω'"=> Need P ( height R s + k )
-- amass cost at seam
include hp ht he hk hF hX h
lemma holdF (hh:n<d): totalT U ( ( F - FrameZ p Ω-nav M P.η ( rootT P M x R s V ) ) n ) Ω' false:= by
    obtain hy:= priceN ( M:= M ) ( R:=R ) ( s:= s ) ( mesh_sep hp ) rfl h hh; let E:= rootT P M x R s; let B:= Physical P.η M p; have hm: F-FrameZ p Ω-nav M P.η ( E V )= E (X-B-A)+( F-E X ) - ( Y-E B ) -( nav M P.η ( E V )-E A ):= by simp only [map_sub]; abel
    rw [hm]; exact FormP.minus ( FormP.minus ( FormP.plus hy (arriveN ( mid_way.tiny ( hF n ) )) ) ( arriveN ( mid_way.tiny ( hX n ) )) ) ( arriveN ( core_nav hp ht hk he.life n ) )
lemma HOLD (hx:∀ i,seatB ( amber P ( height R s + k ) ) (H i) = seatB ( amber P (height R s + k ) ) (rootT P M x R s V i) )(hh:n<d): totalT U ((F-FrameZ p Ω-nav M P.η H) n ) Ω' false:= by
    unfold totalT; rw [ show sendT ( U ) ((F-FrameZ p Ω-nav M P.η H) n)= sendT ( U ) ((F-FrameZ p Ω-nav M P.η ( rootT P M x R s V )) n) from ( by have h:= send_E ( M:=M ) ( P:=P ) ( k:=n ) hx; exact congr_arg (fun V'=> sendT ( U ) (( F- FrameZ p Ω ) n) - V') h ) ]; exact holdF hp ht he hk h hF hX hh -- order args?
include hu
lemma final_P (hx:Response (FrameZ p Ω) M P.η 0) (n:ℕ)(hv:n<d):
    paid (later P (height R s+k)).dawn (fun i=> ‖blade ( (F-FrameZ p Ω) n ) i‖ )
        (Need P (height R s+k)) := by
    let n':ℕ := height R s+k
    obtain ⟨Y0,hP,H0⟩:= soars M (amber P n') P.η ( R_bank ( mesh_sep hp ) he.life s )
    let H := nav M P.η Y0
    have hT : Response H M P.η 0 := hP.ward.1
    have he' := hu.sub hx
    obtain hh:= inclusive (he'.sub hT) ( R:=later P n' ) later_live (later_all P n')
        (fun i hi=> HOLD hp ht he hk h hF hX H0 hi) need_nn n hv
    rw [mergeB he' hT n, show Vane.blade ( H n )=0 from funext (fun i=> closeQ hP i n), sub_zero] at hh
    exact hh

end YM.FVA2.O.Seam
