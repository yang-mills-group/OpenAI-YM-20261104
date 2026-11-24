import YM.FVA2.O.Lives.Resp
import YM.MS.Breeze.Seats
/-!
# Anchors. Tilt a mark at t fixed; cost on arbitrary shape family (*without* uniform norm bound).
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Serve
open MS Function Filter Set Finset MS.Plane MS.Koszul Flux MeasureTheory MS.Heat MS.Book Convolve Signal
open MS.Breeze MS.Latch MS.Native MS.Osc.Snap MS.Osc MS.Fiddle MS.Garment MS.Garment.Wick MS.Rock MS.Rock.Path MS.City MS.Rake MS.Tone Momentum MS.Landau Detect MS.Color Real
open Ward Job Wire MS.Local.Physical MS.Land Lives
open scoped Topology ContDiff
variable {G:Gauge}{B:Deck G}{O:Booked B} {x y:Law G}{I:Type}{F H:Glade G I}{a b:QP}{X:T (Glade G I)}{M:MS_Data G O}{η:I→ℝ}{p q: I→ QP}{r n:ℤ}{i:I}{U:Edge G}
lemma rotate (a:QP)(h:Solid false x n): Solid false (chair G a x) n:= by
    constructor; · intro l i j t hl; rw [ seated, seated,h.symm l i j t hl,mul_left_comm ]; congr 2; apply congr_arg (bill a); simp only [net_append,net_cons]; abel
    · intro w hw hv; rw [seated, h.ghost _ hw hv,mul_zero ]
    · intro w hw u; rw [seated,← h.color w hw u]; let L (g:Law G)(w':List (Lane4 G)):= solo u w' g; change L _ w=Tone.bill a _ * L _ _; clear h; let c:= Tone.bill a ( Plane.net w ); have he(w':List (Lane4 G))(hv: High.paint w' w): chair G a x w'= (c • x) w':= by
          unfold c; change Tone.bill _ _ * _= _; have he (w:List (Lane4 G)) : net (High.undye w)=net w:= by unfold net High.undye; rw [List.map_map]; rfl
          rw [← he w', hv,he]; rfl
      change repeatC u _ _=(c • repeatC u x) _; rw [ ← map_smul ]; exact High.paint_congr u w he
    intro w hw; simp_rw [ seated,h.real' w hw,net_invert,star_mul', Tone.starbill,Tone.inverse,Tone.opp ]
lemma chairQ (K:Charge Landau.parity QP ℂ) : chair G a (K.raise x)=K.raise (chair G a x):= by
    funext l; let c:=bill a (net l); have hp (w)(hm:net w=net l): (c • x) w=chair G a x w:= by rw [seated,hm]; rfl
    change c • K.raise x l= _; rw [show c • K.raise x l=K.raise (c • x) l from ( by rw [map_smul]; rfl ),visit_Z,visit_Z]; apply visit_agree; intro w i k hx; refine Finset.sum_congr rfl (fun j _=> congr_arg _ (hp _ (by rw [← hx,net_append,net_cons,net_append,net_cons])) )
lemma chairL (h:Rolled U)(hp:x∈ Wallet G) : chair G a ( Heat.orbit U planeF x ) = Heat.orbit U planeF (chair G a x):= by
    rw [ finite_cc planeF (h.pays Geo.Coherent hp), finite_cc planeF (h.pays Geo.Coherent ( chair_v a hp )) ]; funext l; unfold Ccy; rw [ seated,← integral_const_mul ]; simp_rw [ at_trc,seated,net_cons, ← add_assoc, add_neg_cancel,zero_add,mul_left_comm ( U _ _ _ ) (Tone.bill _ _),← Finset.mul_sum ]
lemma chairT : chair G a (tree Landau.parity U x y) = tree Landau.parity U x (chair G a y):= by
    funext l; unfold tree; rw [seated]; let P:= allocate (field Landau.parity) l (R:=ℂ); change bill a (net l) • P _=P _; rw [← map_smul]; apply scatter_congr; intro x' y' hp; simp_rw [Pi.smul_apply,smul_eq_mul,attaches, seated,neg_neg, net_cons, split_net hp, Finset.mul_sum ]; apply Finset.sum_congr rfl; intro k _; apply Finset.sum_congr rfl; intro t _; ring
-- morph on all glades. preservation upper
abbrev tilt (G:Gauge)(p:I→QP): MH (Glade G I):= Puff.varied I (fun i=> Puff.varied ℝ (fun _=> chair G (p i)))
lemma tilted : tilt G p F i = fun s=> chair G (p i) (F i s):= rfl
lemma Wtilt (h:Warm F false) : Warm (tilt G p F) false:= by
    constructor; · intro i T hT E _ _ w hw hϕ; let K:= single (camp T); have hp:K.full.Le (fun _ (_:E)=>‖p i‖) (fun t _=> K.length t):= ⟨‖p i‖+1,by positivity,0, fun t q _=>by simp [K, Job.single]⟩; let v:= h.cost i T hT E w hw hϕ; unfold Cape Chart tap; simp_rw [tilted,seated,sail_net]; exact pulse_bill (V:=fun _=> p i) (net w) v hp
    intro i l hx; unfold tilt; exact continuous_const.mul (h.walk i l hx)
lemma Ktilt (h:Diversity F r): Diversity (tilt G p F) r:= fun i v w hw=>by simp_rw [ tilted, seated, h i v w hw,mul_zero ]
lemma bankTilt (h:Bank F n): Bank (tilt G p F) n:= ⟨ Wtilt h.cross,by obtain ⟨k,h⟩:=h.heat; exact ⟨k,Ktilt h⟩, fun i _=> rotate (p i) (h.tone i _)⟩
lemma velTilt (h:Velocity F H) : Velocity (tilt G p F) (tilt G p H):= fun i t w=> ( h i t w ).const_mul _
end YM.FVA2.O.Serve
