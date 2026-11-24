import YM.FVA2.O.Fusion.Pepa
import YM.MS.Dial.Slope
/-!
# Scalar evaluation in IR
No limit of symbols in stronger topology in this lemma.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Fuse
open MS Function Filter Set Finset MS.Plane MS.Koszul Flux MeasureTheory MS.Heat MS.Book Convolve Signal
open MS.Breeze MS.Latch MS.Native MS.Osc.Snap MS.Osc MS.Fiddle MS.Garment MS.Garment.Wick MS.Rock MS.Rock.Path MS.City MS.Rake MS.Tone Momentum MS.Landau Detect MS.Color Real
open Ward Job Wire MS.Local.Physical MS.Land Lives Puff Serve Rake.Geo Vane Actors
open scoped Topology ContDiff Interval
variable {G:Gauge} {I E W:Type} [LinearOrder W]{B:Deck G}{K:Booked B}{M:MS_Data G K}{q:ℤ}{P:Geo I}{x:Position W I}{p a b:I→QP}{R:W→Rake.Label B}{X:Rake.Dance G I W}{S:Finset W}{n:ℕ}
abbrev evaluate (G:Gauge)(i:I)(s:ℝ): Puff.Linear (Glade G I) ℂ:= { toFun F:= F i s [], map_smul' _ _:= rfl,map_add' _ _:= rfl }
omit [LinearOrder W] in
lemma tuft (G:Gauge)(i:I)(s:ℝ): Tether (evaluate G i s) (hori G I) Puff.Mom.Toy:= ⟨rfl,fun _ _=> nil_product ..⟩
lemma η_measure (i:I) (s:ℝ): Meal X S n i s []=Puff.Mom.bouquet (fun k j=> X k j i s []) S n:= congr_fun ((( tuft G i s ).Extrapolation SplitP.nat).figure (SplitP.marked W) X S) n
lemma stamp (i:I)(s:ℝ): untap x X S n i s []= X S n i s []:= by change Tone.bill _ _ * _=_; simp [ net ]
lemma sunrise (i:I)(s:ℝ): plenum x X S n i s []= Puff.Mom.bouquet ( fun k j=> X k j i s [] ) S n:= by simp only [plenum,η_measure,stamp]
lemma posed (h:DOrd K P M R x X) (i:I) (hX:Injective (Dial.pointI x i)): X S n i= Dial.spine M R (P.η i) (Dial.pointI x i) S n ():= by
    have ht:= Dial.valid_copy R h (fun (_:Unit)=>i) ( Q:=Tide.frameF Unit ( P.η i ) ) ( fun _=>rfl ); obtain hp: Dial.spine M R (P.η i) (Dial.pointI x i)= Dial.copy (fun (_:Unit)=>i) X:= perfect ( Dial.pin M R (P.η i) hX ) ht; rw [hp]; rfl
variable (h:DOrd K P M R x X)(i:I)(ht:Injective (Dial.pointI x i))
include h ht
lemma tenue (s:Finset W) (n:ℕ) : Tendsto (fun v:ℝ=> X s n i v []) atTop ( 𝓝 ( Dial.book M R (P.η i) ( Dial.pointI x i ) s n )) := by
    let Y:= Dial.spine M R (P.η i) ( Dial.pointI x i ); by_cases hs:s.Nonempty
    · have hp: Mesh (Tide.frameF Unit ( P.η i )) (fun k (_:Unit)=>x k i):= by intro u v hu; obtain ht:0< ‖x u i-x v i‖:= norm_pos_iff.mpr (sub_ne_zero.mpr (ht.ne hu)); refine ⟨⟨_,ht,fun p=> ?_⟩,⟨_,ht,fun p=> ?_⟩⟩ <;> simp [ roots ]
      rw [posed h _ ht]; exact (Dial.reports R hp ( Dial.pin M R _ ht ) hs n).1 ()
    rw [Finset.not_nonempty_iff_eq_empty.mp hs]; unfold Dial.book; rw [h.1,( Dial.pin M R _ ht ).1]; obtain h:Vane.blade (0:Glade G Unit) ()=0:= ( Fleet.allow_zero _ ).2; simp only [ Pi.zero_apply,h ]; exact tendsto_const_nhds
lemma ready (s:Finset W)(n:ℕ): Tendsto (fun v:ℝ=> plenum x X s n i v []) atTop (𝓝 ( Dial.tour M R ( P.η i ) (Dial.pointI x i) s n )):= by simp_rw [sunrise]; exact Puff.Mom.Accord.select (f:=fun v:ℝ=> fun s n=> X s n i v []) (fun s n=> tenue h i ht s n) s n -- mk? change
end YM.FVA2.O.Fuse
