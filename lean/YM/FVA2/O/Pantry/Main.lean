import YM.FVA2.O.Pantry.Patch
import YM.FVA2.O.Dust.Point
import YM.FVA2.O.Rough.Peak
/-!
# Full product assertions also on unbounded sets of separated configurations

Use only pointwise separation in this `Rake` geometry. Then identify
`Dial.tour` with the scalar IR limit here, and apply the exact Ward results
on these product inputs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Price
open MS Function Filter Set Finset MS.Plane MS.Koszul Flux MeasureTheory MS.Heat MS.Book Convolve Signal
open MS.Breeze MS.Latch MS.Native MS.Osc.Snap MS.Osc MS.Fiddle MS.Garment MS.Garment.Wick MS.Rock MS.Rock.Path MS.City MS.Rake MS.Tone Momentum MS.Landau Detect MS.Color Real MS.Tide
open Ward Job Wire MS.Local.Physical MS.Land Lives Serve Rake.Geo Vane Fuse Puff
open scoped Topology ContDiff Interval
open Cool Rough
variable {G: Gauge}{I J:Type} { P:Geo I } {W:Type}[LinearOrder W] {B:Deck G}{K: Booked B}{M:MS_Data G K}{X:Rake.Dance G I W}{s: Finset W} {x:Position W I} {r:W→Rake.Label B}
local notation "Pos"=> Dial.pointI
omit [LinearOrder W] in
abbrev screen (G:Gauge)(θ:J→I): Puff.Linear (Glade G I) (Glade G J) := { toFun:= fun i=> i∘θ,map_smul':=fun _ _=> rfl, map_add':=fun _ _=> rfl }
omit [LinearOrder W] in
lemma screen_m (θ:J→I) : Tether (screen G θ) (hori G I) (hori G J) := ⟨rfl,fun _ _=>rfl⟩
lemma screen_F (θ:J→I): compose0 θ (Meal X s)=Meal (snap_c θ X) s:= ((screen_m θ).Extrapolation SplitP.nat).figure (SplitP.marked W) X _
lemma screen_s (θ:J→I): untap (fun k=> x k ∘ θ) ( snap_c θ X ) = snap_c θ (untap x X):= by funext s n i; change ( tilt _ _ _) _=_; rw [ Dial.basis_copy x θ ]; rfl -- rootX may need `∘`
lemma screen_P (θ:J→I): compose0 θ (plenum x X s)= plenum (fun k=>x k ∘θ) ( snap_c θ X ) s:= by unfold plenum; rw [screen_F]; rw [screen_s]
lemma screen_r (θ:J→I): compose0 θ ( resin x X s )= resin (fun k=> x k ∘ θ) ( snap_c θ X ) s:= by
    have hh : snap_c θ (wax (untap x X))=wax (untap (fun k=> x k ∘ θ) ( snap_c θ X )):= by funext s; rw [screen_s θ]; unfold wax snap_c Dial.copy; dsimp only; split <;> rfl -- defeq
    unfold resin; rw [screen_F,hh]
omit [LinearOrder W] in
lemma point_m (h:separable x)(p:I): Mesh (frameF Unit (P.η p)) (fun w (_:Unit)=>x w p):= by
    intro i j he; have hp : 0< ‖x i p-x j p‖:=norm_pos_iff.mpr (sub_ne_zero.mpr (h p |>.ne he)); refine ⟨⟨_,hp,fun i=>?_⟩,⟨_,hp,fun i=>?_⟩⟩ <;> simp [roots]
omit [LinearOrder W] in
lemma tick (p:I) (x:Position W I)(k:W): Fixed ( fun (_:Unit)=> x k p ):= ⟨ ‖x k p‖+1,by positivity,fun _=>by linarith ⟩
variable (h:separable x) (ht:DOrd K P M r x X)
include h ht
omit h in
lemma point_v (p:I): DOrd K (frameF Unit (P.η p)) M r (fun k=>x k ∘ fun (_:Unit)=>p) (snap_c (fun (_:Unit)=>p) X):= Dial.valid_copy r ht _ (fun _=>rfl)
lemma a_warm (s:Finset W)(n:ℕ): Warm ( X s n ) false:= ⟨ fun i=> ( world_price (point_m h i) (point_v ht i) s n ).cost (), fun i=> ( world_price (point_m h i) (point_v ht i) s n ).walk ()⟩
lemma advance_r : Certified (plenum x X s) M P.η 0 := by
    refine ⟨ plenum_R ht ( a_warm h ht ) s,?_ ⟩; funext n i; let θ (_:Unit):=i; suffices H : compose0 θ ( nav M P.η ( plenum x X s ) )= 0 from congr_fun ( congr_fun H n ) (); rw [ ← nick, screen_P ]; exact (safe_Ward ( point_m h i ) rfl ( tick i x ) ( point_v ht i ) s ).2
lemma ahead_n (p:I): Sweep (frameF Unit ( P.η p )) ( compose0 (fun (_:Unit)=>p) (plenum x X s - resin x X s) ):= by
    let θ (_:Unit):=p;
    have hx : compose0 θ (plenum x X s - resin x X s) = compose0 θ (plenum x X s) - compose0 θ (resin x X s):= rfl; change Sweep _ (compose0 θ _); rw [ hx, screen_P,screen_r ]; exact sents (point_m h p) rfl ( point_v ht p ) (tick p x) s
lemma blade_t (i:I)(n:ℕ): blade (plenum x X s n) i= Dial.tour M r ( P.η i ) ( Pos x i ) s n:= tendsto_nhds_unique ( total_peak (advance_r h ht).1 i n ) ( Fuse.ready ht i ( h i ) _ _ )
end YM.FVA2.O.Price
