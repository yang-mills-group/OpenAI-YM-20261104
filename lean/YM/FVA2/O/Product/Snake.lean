import YM.FVA2.O.Product.Chairs
/-!
# All mark arguments at same center
 No momentum conservation is imposed. Commute shift and response.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Serve
open MS Function Filter Set Finset MS.Plane MS.Koszul Flux MeasureTheory MS.Heat MS.Book Convolve Signal
open MS.Breeze MS.Latch MS.Native MS.Osc.Snap MS.Osc MS.Fiddle MS.Garment MS.Garment.Wick MS.Rock MS.Rock.Path MS.City MS.Rake MS.Tone Momentum MS.Landau Detect MS.Color Real
open Ward Job Wire MS.Local.Physical MS.Land Lives
open scoped Topology ContDiff
variable {G:Gauge}{B:Deck G}{O:Booked B} {x y:Law G}{I:Type}{F H:Glade G I}{p q: I→ QP}{X:T (Glade G I)}{M:MS_Data G O}{η:I→ℝ}{r n:ℤ}
abbrev swing (G:Gauge)(p:I→ QP): MH (T (Glade G I)):= promote (tilt G p)
lemma upright : tilt G (p+q) F= tilt G p (tilt G q F):= funext (fun _=> funext fun _=> (climb _ _).symm)
lemma dizzy : tilt G 0 F=F:= funext fun _=> funext fun _=> faith_m
lemma easy (p:I→QP) (F:Glade G I): tilt G (-p) (tilt G p F)=F:= by rw [← upright,neg_add_cancel,dizzy]
lemma fly_P (h:Warm F false): tilt G p ( ( both G I ).P F )=(both G I).P (tilt G p F) := funext fun i=> funext fun t=> chairL rA (Wallet.awake h i t)
lemma fly_J (h:Warm F false): tilt G p ((both G I).J F)=(both G I).J (tilt G p F):= by
    funext i t; change chair G (p i) ((Q G 0).raise _+Heat.orbit _ _ _)=_; rw [map_add,chairL (U:=lineB G t) rB (Wallet.awake h i t),chairQ]; rfl
lemma fly_T : tilt G p ((both G I).X F H)=(both G I).X F (tilt G p H):= funext fun _=> funext fun _=> chairT
lemma fly_U : tilt G p ((both G I).C F H)=(both G I).C F (tilt G p H):= funext fun _=> funext fun _=> chairT
lemma helion (h:∀ n, Warm (X n) false): swing G p ( helm M η X ) = helm M η ( swing G p X ) := by
    funext n; simp only [helm, swing,promised,LinearMap.add_apply,Pi.add_apply,paired,map_add,map_sum]; simp_rw [fly_P (h _),fly_T]
lemma nax (h:∀ n,Warm (X n) false): swing G p (nav M η X) = nav M η (swing G p X ) := by
    funext n; simp only [nav, swing,promised,LinearMap.add_apply,Pi.add_apply,paired,map_add,map_sum]; simp_rw [fly_J (h _),fly_U]
lemma snakeV (h:Response X M η r): Response (swing G p X) M η r where
    life n:= bankTilt (h.life n)
    vital n:= by rw [ ← helion ( fun i=>(h.life i).cross ) ]; exact velTilt (h.vital n)
lemma snake (h:Certified X M η r): Certified (swing G p X) M η r:= ⟨snakeV h.1,by rw [← nax ( fun n=> (h.1.life n).cross), h.2,map_zero] ⟩
end YM.FVA2.O.Serve
