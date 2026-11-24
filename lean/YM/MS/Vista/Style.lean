import YM.MS.Vista.Window
/-!
# Lease wrappers with memory pre-clocked. Holds post truncation with h=tail too.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Vista
open Set Function Filter Finset Metric MeasureTheory Real High
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Osc.Snap Native Lattice City Latch Job Belt Rake Flux Wire Book Convolve Orbit
open Rake.Geo
open scoped Topology ContDiff Interval
variable {I E:Type}{G:Gauge}{P:Belt I}{ M: Visa I }{μ:P.time→Measure QP}{ Z:Lin I}
    {b c:Bool}{a x y:P.time→ℝ}{ A B:Faces I}{X Y:Glade G I}{K:Planet G I}{n:ℕ}
-- static budget wrappers across dynamic scheme νZ & μ1
abbrev omegaV (P:Belt I)(Z:Lin I)(μ:P.time→Measure QP):= VistaQ P.price (Ap P Z.circ) μ
def Vel (P:Belt I)(Z:Lin I)(K:Planet G I)(μ:P.time→Measure QP)(A:P.time→ℝ): Prop:= omegaV P Z μ ∧ Piece P K A ∧ nn A
abbrev SpanW (b:Bool)(Z:Belt I)(F:Glade G I):= coinF b Z (warp0 G I F)
abbrev Spd (b:Bool)(Z:Belt I)(F:Glade G I):= coinF b Z (bend G I F)
abbrev HandC (b c:Bool)(Z:Belt I)(F:Glade G I):= Here b c Z (bend G I F)
variable (H:Vel P Z K μ a)
include H
lemma On_c (h:SpanW c P X x (n+2))( he:Toned X)(hp:nn x)(hh:b=true→ c=false): Spd c P (click Z b A K X) ( a * x ) n:= by
    unfold Spd coinF; rw [ wc_click ]; exact p_pay H.1 ( H.2.1 b ) ( footage X he ) hh h H.2.2 hp -- scope.Perkin valid.
lemma driveS (hF: WarpHere true true P X x)(hH:WarpHere b true P Y y)(hx:nn x)(hy:nn y): HandC b false P ( expJ K X Y ) ( positive P.price 4 a (x*y) ):= by unfold HandC Here; rw [expP]; exact trunks ( H.2.1 false |>.cost.1 ) hF hH H.2.2 hx hy
lemma η_body (hx:WarpHere true true P X x)(he:Toned X)(hM:nn x): HandC false false P (term_birth K X) ( positive P.price 4 a x ):= by
    unfold HandC Here; rw [ weightFC ]; obtain hm:= H.2.1 true; exact pocket hm.room hm.cost hm.perk ( footage X he|>.1 ) hx H.2.2 hM
lemma BookOn (W:P.time→ℝ)(h: Radar P.price W (Ap P (env b A B)) μ)(he: Mileage P.price (Ap P ( A-B )) W)(hz:∀ i,P.price.length i ≤ W i)(hF:WarpHere false true P X x)(hH: WarpHere false true P Y y) ( hp:Toned X )( hv:Toned Y )( hx:nn x )( hy:nn y )(k:ℕ): HandC false false P (feeling Z b A B K X Y) (Growth P.price W (a*x*y) k):= by unfold HandC Here; rw [wc_region]; exact farMesh (H.2.1 b) (footage X hp) (footage Y hv) hF hH hx hy H.2.2 H.1 h he hz k -- hp
lemma Honor (h:Mileage P.price (Ap P (A-B)) P.price.length)(hF:WarpHere false true P X x)(hH:WarpHere false true P Y y)(hv:Toned X)(hx:Toned Y)(hp:nn x)(hu:nn y): HandC false false P (feeling Z b A B K X Y) (a*x*y):= by unfold HandC Here; rw [wc_region]; exact murmur hF hH (H.2.1 _) H.1 (footage X hv) (footage Y hx) h hp hu H.2.2
lemma Bolt (h: SpanW false P X x (n+2))(hz:Toned X)(hv:nn x): Spd false P (zip0 Z K A X) (a*x) n:= by
    unfold zip0; by_cases H':Z.orbit; · rw [ adjust, if_pos H' ]; unfold Spd; rw [ map_add ]; exact Lens.plus ( On_c (b:=false) H h hz hv (fun h=>rfl)) ( On_c (b:=true) H h hz hv (fun _=>rfl) ) -- binder shadow.P.
    rw [adjust,if_neg H',add_zero ]; exact On_c H h hz hv (fun _=>rfl)
omit H in
lemma Fund_slot {I:Type}{P:Scale I}{K:I→ Latch.Edge G}{a b:I→ℝ}(hp:Fund P K a)(h:∀ i,a i≤ b i): Fund P K b:= by
    refine ⟨ ⟨fun i j=> (hp.cost.1 i j).raise (Cost.of_le fun i p _=>?_ ), fun i j=> (hp.cost.2 i j).monotone ?_ ⟩,hp.perk,hp.room ⟩; · exact mul_le_mul_of_nonneg_left (h i) (length_p ..)
    exact fun i=> mul_le_mul_of_nonneg_left ( h i ) (length_p ..)
lemma Vel.up (hz:a≤ x): Vel P Z K μ x:= ⟨ H.1,fun b=> Fund_slot ( H.2.1 b ) hz,fun i=>( H.2.2 i ).trans ( hz i ) ⟩
omit H in
lemma mileage0 (A:Faces I): Mileage P.price (Ap P ( A-A )) P.price.length:= paidMono fun i=>by simp [ Ap,show embed 0=0 from (by ext; simp [embed])]; exact (P.price.pos i|>.le)
lemma spin_d (hF:WarpHere false true P X x)(hH:WarpHere false true P Y y)(hv:Toned X)(hx:Toned Y)(hp:nn x)(hu:nn y): HandC false false P (zip2 Z K A A X Y) (a*x*y):= by
    unfold zip2; have he (x:Bool):= Honor (A:=A) (B:=A) (b:=x) H (mileage0 A) hF hH hv hx hp hu; by_cases hm : Z.orbit; · rw [adjust,if_pos hm]; unfold HandC; rw [map_add]; exact Lease.plus (he false) (he true)
    rw [adjust,if_neg hm,add_zero]; exact he false
end YM.MS.Vista
