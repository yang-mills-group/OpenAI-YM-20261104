import YM.FVA2.Extras.Result
import YM.FVA2.Smooth.Point
/-!
# Actual coordinate-derivative charges represent physical insertions

 For the Extra reduction use the *resolved* fields, specialized four-dimensional in
 the precise MS_Data scheme. We can literally differentiate single marked insertions
 and keep the scaled power (augment grade by one). This holds at every fixed `a=logν`,
 at arbitrary order (not just the free-price tail). Will be used to prove the optional
 smooth shape enhancement of this OPE.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.DerivD
open MS Function Filter Set Finset MS.Plane MS.Koszul Flux MeasureTheory MS.Heat MS.Book Convolve Signal
open MS.Breeze MS.Latch MS.Native MS.Osc.Snap MS.Osc MS.Fiddle MS.Garment MS.Garment.Wick MS.Rock MS.Rock.Path MS.City MS.Rake MS.Tone Momentum MS.Landau Detect MS.Color Real O
open Ward Job Wire MS.Local.Physical MS.Land O.Lives O.Serve FVA2.Extras Smooth Smooth.Lifetime MS.Motif
open scoped Topology ContDiff Interval BigOperators
variable {G:Gauge}{B:Deck G}{O:Booked B}{M:MS_Data G O}{F F' H:Law G}{I:Type}{X Y:Glade G I}{U:T ( Glade G I )}{η:I→ℝ}{a:ℝ}{n r:ℤ}{E: Edge G}
abbrev facetM (v:Axis) : MH (Law G) := moment ( Lifetime.turn v ).toLinearMap.toAddMonoidHom
lemma inked (i: Axis) (he:Solid false F n): Solid false (facetM i F) n := by
    let s:= ( Lifetime.turn i ).toLinearMap.toAddMonoidHom; constructor; -- port from rotate
    · intro l i j t hl; rw [facetM,moon,moon,he.symm l i j t hl,mul_left_comm]; congr 2; -- set
      simp only [net_append,net_cons]; apply congr_arg s; abel
    · intro w hw hv; rw [facetM,moon, he.ghost _ hw hv,mul_zero]
    · intro w hw u; rw [facetM,moon,← he.color w hw u]; let L (g:Law G)(w':List (Lane4 G)):= solo u w' g; let c:= s ( Plane.net w ); change L (moment s F) w= c * L _ _;
      have he(w':List (Lane4 G))(hv: High.paint w' w): moment s F w'= (c • F) w':= by
          unfold c; change _=s _*_; rw [moon]; have he (w:List (Lane4 G)): net (High.undye w)=net w:= by unfold net High.undye; rw [List.map_map]; rfl
          rw [← he w', hv,he]
      change repeatC u _ _=(c • repeatC u F) _; rw [ ← map_smul ]; exact High.paint_congr u w he
    intro w hw; change ( moment s F ) _=star _; simp_rw [moon,he.real' w hw,net_invert,map_neg,star_mul']; change -( Lifetime.turn _ _ ) * _=star ( Lifetime.turn _ _ ) * _; simp [Lifetime.turn_eq]
-- tautological.
lemma strand (i:Axis)(hX:Bank X n): Bank (Lifetime.force i X) n:= ⟨ Lifetime.hot i hX.cross, Lifetime.onlyT i hX.heat, fun j k=> inked i ( hX.tone j k )⟩
abbrev pole_ξ (i:Axis)(G:Gauge)(I:Type): MH (Glade G I):= MS.Puff.varied I (fun _=> MS.Puff.varied ℝ (fun _=>facetM ( G:=G ) i))
lemma raises (K:Charge Landau.parity QP ℂ) (i:Axis) : facetM i ( K.raise F )=K.raise (facetM i F):= by
    funext l; let c:=Lifetime.turn i (net l); have hp (w)(hm:net w=net l): (c • F) w=facetM i F w:= by rw [ facetM,moon,hm ]; rfl
    change c • K.raise F l= _; rw [show c • K.raise F l= K.raise (c • F) l from ( by rw [map_smul]; rfl ),visit_Z,visit_Z]; apply visit_agree; intro w j k hx; refine Finset.sum_congr rfl (fun j' _=> congr_arg _ (hp _ (by rw [← hx,net_append,net_cons,net_append,net_cons])) )
lemma speedy (ht:Rolled E)(hV:F∈ Wallet G)(i: Axis)(hp: facetM i F∈Wallet G): facetM i ( Heat.orbit E planeF F ) = Heat.orbit E planeF ( facetM i F ):= by
    rw [finite_cc planeF (ht.pays Geo.Coherent hV), finite_cc planeF (ht.pays Geo.Coherent hp) ]; funext l; unfold facetM Ccy; rw [moon,← integral_const_mul ]; simp_rw [at_trc,moon,net_cons, ← add_assoc, add_neg_cancel,zero_add, mul_left_comm ( E _ _ _ ), ← Finset.mul_sum ]; -- `mul_left_comm` needs all second arg fixed
abbrev stage (i:Axis)(G:Gauge)(I:Type) := promote (pole_ξ i G I)
lemma forceP (i:Axis)(h:Warm X false): pole_ξ i G I ( (both G I).P X )=(both G I).P (pole_ξ i G I X):= funext fun _=> funext fun t=> speedy rA (Wallet.awake h _ t) i ( Wallet.awake (Lifetime.hot i h ) _ t )
lemma forceJ (i:Axis)(h: Warm X false): pole_ξ i G I ( (both G I).J X )=(both G I).J (pole_ξ i G I X):= by
    funext j t; change facetM i (( Wick.Q G 0 ).raise _ + Heat.orbit _ _ _)=_; rw [ map_add,speedy ( E:=lineB G t ) rB (Wallet.awake h j t) i ( Wallet.awake (Lifetime.hot i h ) j t ), raises ]; rfl
lemma forceX (i:Axis): pole_ξ i G I ( ( both G I ).X Y X )=(both G I).X Y (pole_ξ i G I X):= funext fun _=> funext fun _=> ( Lifetime.commuteC ( p:=Lifetime.turn i ) ).symm
lemma forceC (i:Axis): pole_ξ i G I ( (both G I).C Y X )= (both G I).C Y ( pole_ξ i G I X ):= funext fun _=> funext fun _=> ( Lifetime.commuteC (p:= Lifetime.turn i ) ).symm
lemma stage_I (i:Axis)(he:∀ n,Warm (U n) false): stage i G I ( helm M η U ) = helm M η (stage i G I U):= by
    funext n; simp only [helm, stage,promised,LinearMap.add_apply,Pi.add_apply,paired,map_add,map_sum]; simp_rw [forceP i (he _),forceX]
lemma stage_N (i:Axis)(he:∀ n,Warm (U n) false): stage i G I (nav M η U)=nav M η (stage i G I U):= by
    funext n; simp only [nav, stage,promised,LinearMap.add_apply,Pi.add_apply,paired,map_add,map_sum]; simp_rw [forceJ i (he _),forceC]
lemma stays (i:Axis)(hV:Certified U M η n): Certified (stage i G I U) M η n:= by
    refine ⟨ ⟨ fun n=> strand i (hV.1.life n), fun n=>?_⟩, ?_⟩
    · rw [ ← stage_I _ (fun i=> (hV.1.life i).cross) ]; intro j t w; exact ( hV.1.vital n j t w ).const_mul _
    rw [ ← stage_N _ (fun i=>(hV.1.life i).cross),hV.2, map_zero]
lemma Forth.raised (X:T (Glade G Unit))(i:Axis)(hV:Forth a M X n): Forth a M (stage i G Unit X) (n+1):= by
    refine ⟨ stays i hV.1, fun k=>?_ ⟩
    obtain hT:= Lifetime.hot_h i (FullEra a).toScale ( hV.2 k ); unfold Clean; convert! hT using 1 -- adjust
    ext n; simp [neg_add_rev,zpow_add₀ ((FullEra a).pos n).ne' ]
lemma safe {u:ℝ} (v:Rake.Label B)(l:List Axis): Forth u M ( Slots.beamH M ( Tide.frameF Unit u ) v l ) ( ((v.h+l.length): ℕ ) :ℤ ):= by
    induction l with
     | nil=> exact ⟨ Certified.first v.item, cometClean ( M.markOK v.h v.item ) ⟩
     | cons i l ih=> exact Forth.raised _ i ih
end YM.FVA2.DerivD
