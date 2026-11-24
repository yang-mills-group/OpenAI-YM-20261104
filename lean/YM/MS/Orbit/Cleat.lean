import YM.MS.Orbit.Loom
/-!
# Ext memory global all compact times. $Gear Frames.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Orbit
open Set Filter Function Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Snap Native Lattice City Latch Flux Cog Wire
open Job Belt Rake
open scoped Topology ContDiff Interval
variable {I G':Type}{G:Gauge}{F H: Glade G I}{K L: Planet G I}{n:Side}{h r:ℤ}{P: Finset G'}
def uniform (G:Gauge)(I:Type): Planet G I:= fun _=> LaceL G
structure Lin (I:Type) where
   circ : I→Measure QP
   orbit: Bool
   side : I→ Side
   finite_q i: IsFiniteMeasure (circ i)
   limits : ∀ i,Cour (circ i)
variable {Z:Lin I}
structure Glow (P:Planet G I): Prop where
   flexW : ∀ i,flex ( P i )
   proper (i) t : Twig ( P i t )
lemma healthy (G:Gauge)(I:Type) : Glow (uniform G I):= ⟨fun _=> flexD ( main_f _ ),fun _ t=> foe G t ⟩ -- i implicit unused
abbrev PaintP (b:Bool)(P:Planet G I): Planet G I:= fun i t=> ηbone b ( P i t )
def enterV (L:I→Side)(b:Bool): Lin I:={
   circ i:=σcap (periodN ( L i ))
   orbit:= b
   side:= L
   finite_q _:=finite_s _
   limits _:= cour_s _ }
abbrev outside (L:I→Side): Lin I:= ⟨ fun _=>μzone,false,L,fun _=>inferInstance,fun _=> cour0⟩ -- zone.Cost
instance (Z:Lin I)(i:I): IsFiniteMeasure (Z.circ i):= Z.finite_q i
lemma passθ (h:Glow K)(b:Bool)(i:I): flex ( PaintP b K i ):= flex_η b ( h.flexW i )
lemma pin_θ (h:Glow K)(b:Bool)(i:I)(t:ℝ): SpeaksK ( PaintP b K i t ):= by cases b; exact h.proper .. |>.pin; exact picture ( h.proper ..|>.pin )
structure Toned (F:Glade G I): Prop where
    touch i: TouchF (F i)
    sound i t : Speaks ( F i t )
abbrev Knits (F:Glade G I): Prop:= Toned F ∧ collect F
lemma Tone0 (G:Gauge)(I:Type): Toned (0:Glade G I):= ⟨ fun _=> TouchF.zeros, fun _ _ => speak0 ⟩
lemma Tplus (hF:Toned F)(he:Toned H): Toned ( F+H ):= ⟨fun i=> (hF.touch i).add (he.touch i),fun i t=> speak_add (hF.sound i t) ( he.sound i t)⟩
lemma Tsum {F:G'→Glade G I}(P:Finset G')(h:∀ i∈ P,Toned (F i)): Toned (∑ i∈P,F i):= by classical induction P using Finset.induction with| empty=> rw [Finset.sum_empty]; exact Tone0 ..| insert i P hp ih=> rw [Finset.sum_insert hp]; exact Tplus (h i (by simp)) (ih fun i hi=> h i (by simp [hi]))
lemma Trun (h:Toned F)(c:ℂ): Toned ( c • F ):= ⟨ fun i=> ( h.touch i ).scale c,fun i t=> speak_smul (h.sound i t) c ⟩
lemma knit0 (G:Gauge)(I:Type): Knits (0:Glade G I):= ⟨ Tone0 ..,collect_z ⟩
lemma knit_plus (h: Knits F)(hf:Knits H): Knits ( F+H ):=⟨ Tplus h.1 hf.1,collect_p h.2 hf.2 ⟩
lemma knit_smul (h:Knits F)(c:ℂ): Knits ( c • F ):= by obtain ⟨h,k,hK⟩:= h; exact ⟨ Trun h c,k,fun i t=> (hK i t).smul c ⟩
lemma knit_sum {F:G'→Glade G I}(P:Finset G')(h:∀ i∈P, Knits (F i)): Knits (∑ i∈P,F i):= ⟨ Tsum _ (fun i hi=>(h i hi).1), collected _ fun i hi=> ( h i hi).2 ⟩
variable {v: I→Cover}
-- abstract programs.Bullet orientation
abbrev click (Z:Lin I)(b:Bool)(v:I→Cover)(P:Planet G I)(X:Glade G I): Glade G I:=fun i t=> Θ_pc b (Z.circ i) (v i) (PaintP b P i t) ( X i t )
abbrev feeling (Z: Lin I)(b:Bool)(u v:I→Cover)(P:Planet G I)(F H:Glade G I): Glade G I:= fun i t=> PairV b (Z.circ i) (u i-v i) (Dph b (u i) (v i)) (PaintP b P i t) (F i t) (H i t)
lemma loopT (Z:Lin I)(b:Bool)(v)(hF:Toned F)(hp:Glow K): Toned ( click Z b v K F ):= ⟨ fun i=> p_pc (h:=Z.limits i) b (v i) ( passθ hp b i ) (hF.touch i),fun i t=> Θ_per _ b _ _ ( hF.sound i t ) ⟩ -- param order.Compile
lemma airEngine (v)(b:Bool): Engine ( click Z b v K ):= by
    refine ⟨fun r F H h i t w hw=>?_,?_ ⟩; · unfold click Θ_pc; simp_rw [show ∀ i' j': Lane4 G, F i t (i'::j'::w)= H i t (i'::j'::w) from fun i' j'=> h i t _ (by simp; omega)]
    funext i t w; unfold click Θ_pc; simp
lemma Cplus (Z:Lin I)(b:Bool)(v:I→Cover)(hp:Glow K)(hF:Toned F)(hh:Toned H): click Z b v K ( F+H )=click Z b v K F+click Z b v K H:= by
    ext i t l; have hu (F:Glade G I) (h:Toned F):= βwait (Z.limits i) b (v i) (passθ hp b i) (h.touch i) l t; simp_rw [click, Θ_pc,Pi.add_apply,mul_add,Finset.sum_add_distrib, mul_add]; exact integral_add (hu F hF ) ( hu H hh )
lemma knit_tree (hp:Glow K)(hf:Knits F)(he:Knits H): Knits ( expJ K F H ):= by refine ⟨ ⟨fun i=> tree_touch (fun t=> (hp.proper i t).t ) (hp.flexW i) (hf.1.touch i) (he.1.touch i), fun i t=> pin_T ( hp.proper i t |>.pin ) ( hf.1.sound i t ) ( he.1.sound i t ) ⟩, collect_tree K hf.2 he.2⟩
lemma pair_cut (u v)(b:Bool)(hp:Diversity F h)(hv:Diversity H r): Diversity (feeling Z b u v K F H) ( h+r-2 ):= by
    intro i t w hw; unfold feeling PairV; refine Eq.trans (scatter_congr _ _ _ (fun l r=>0) (fun x y he=>?_)) (map_zero (allocate ( field parity) w)); obtain hj:= Plane.split_net he; obtain hx:= Koszul.split_length he -- check
    simp_rw [viν]; cases ( show (x.length:ℤ)+1>h ∨ ( y.length:ℤ)+1>r from (by omega)) with | inl h=> simp_rw [ show ∀ c: Lane4 G,F i t ( c::x )=0 from fun c=>hp i t _ (by simp only [List.length_cons,Nat.cast_add,Nat.cast_one]; omega) ]; simp | inr h=> simp_rw [ show ∀ c: Lane4 G,H i t (c::y)=0 from fun c=>hv i t _ (by simp only [List.length_cons,Nat.cast_add,Nat.cast_one]; omega) ]; simp
lemma knit_feeling (hp: Glow K)(hF: Knits F)(hh: Knits H)(A B)(b:Bool)(Z: Lin I) : Knits ( feeling Z b A B K F H ):= by
   obtain ⟨hF,k,hK⟩:=hF; obtain ⟨hh,v,hL⟩:=hh; refine ⟨ ⟨ fun i=> harbor (Z.limits i) b _ _ (passθ hp b i) ( hF.touch i ) ( hh.touch i ), fun i t=> pair_per b _ _ _ ( hF.sound i t ) ( hh.sound i t ) ⟩, k+v, behind ( pair_cut _ _ b hK hL ) (by omega )⟩
abbrev term_birth (K:Planet G I)(F:Glade G I): Glade G I:=fun i t=> birth (valueI ( K i t )) ( F i t )
lemma knit_birth (hF:Knits F)(he:Glow K): Knits (term_birth K F):= by
   obtain ⟨h,m,H⟩:= hF; refine ⟨ ⟨fun i=> qBirth ( flexI ( he.flexW i ) ) (h.touch i), fun i t=> birth_pin ( picture ( he.proper i t |>.pin )) (h.sound i t)⟩,m,fun i t l hl=>?_⟩; unfold term_birth birth detach Hβ; simp_rw [ show ∀ u v:Lane4 G,F i t (u::v::l)=0 from fun u v=> H i t _ (by simp only [List.length_cons,Nat.cast_add,Nat.cast_one]; omega) ]; simp
end YM.MS.Orbit
