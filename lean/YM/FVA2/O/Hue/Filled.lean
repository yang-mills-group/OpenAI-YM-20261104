import YM.FVA2.O.Hue.Steps
import YM.FVA2.O.Dust.Point
/-!
# Approximate an input product in the MS scheme

`field_whole`: for inner insertions in fixed unit geometry (P.θ=0), with separation as in
`Mesh`. At orders < d, decompose into
`Physical` (fields through weight k, with `Valid` coefficient budgets) plus
exact (`nav` at this MS input, on a ghost-degree minus one generator), up to
a `Colorable` error (with `paidC` bounds on log-scale t≥0). Foundation for the
FAR OPE estimate. Here the subsequent exterior argument is *not yet* present.
See `O/Seam/{End,Loom}` and `O/Enh/Sale`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Hue
open MS Function Filter Set Finset MS.Latch Job MS.Plane MeasureTheory Real Metric
open Heat LogTime IntervalFamily Koszul Tone Momentum Landau Fiddle Osc Snap Wire Signal
open Flux Book High Detect MS.Color MS.Local.Physical MS.Land Domain Convolve
open Lives O.Ward MS.City MS.Rake Outlook Tune O.Pad O.Cool O.Fuse Rake.Geo
open MS.Vane
open scoped Topology ContDiff
variable {I:Type}{G:Gauge}{B:Deck G}{K:Booked B}{M:MS_Data G K}{P:Geo I}{X:T (Glade G I)}{F:Glade G I}
def Station (P:Geo I):IntervalFamily I:={
    beg:=0
    beg_nn _:= le_rfl
    window _:= Set.Ici 0
    ci _:=Subset.rfl
    used _:= Set.mem_Ici.mpr le_rfl
    ord _:=ordConnected_Ici
    logPart i:= habitat P i
    lg i:= by simp [habitat] }
lemma liveS : LiveR (Station P) P.η:= ⟨rfl,fun _=>rfl,fun _=>le_add_of_nonneg_left zero_le_one⟩
lemma zero_book (h:Fairy P F): prime (Station P) F:= by
    obtain ⟨b,h⟩:= h; intro E _ _ w hp hx; let v (i:I):=( show (Below P).time from ⟨i,0,le_refl (0:ℝ)⟩ ); have hb(i:I): (Lower P).length (v i)=1:= by rw [ coldE P ]; exact Real.exp_zero; -- folding
    have hη(i:I): (Lower P).basic (v i)= (Station P).dawn.basic i:= by change habitat P i* (1+|(0:ℝ)|) = habitat P i*(1+0); rw [abs_zero]
    have hh:= h E w; let U:=(Station P).dawn; have hl(i:I): (Station P).dawn.length i=1:= Real.exp_zero; refine ⟨ fun i=>hh.smooth (v i),fun j=>?_⟩; obtain ⟨C,hC,k,hk⟩:= hh.quoted j; refine ⟨ _,hC,k,fun i p hp=> le_trans ( hk (v i) p trivial ) ?_⟩; dsimp only; rw [show (Lower P).full.cheap (v i) p= U.full.cheap i p from ?_]; · apply le_of_eq; unfold Qbud Cool.stamp; rw [hb,cw]; simp [Station,U]
    change (Lower P).basic ( v i )* _ = ( Station P).dawn.basic i * _; rw [ hη ]; unfold Scale.weight; rw [hb,hl]
variable {W:Type}[LinearOrder W]{x:Position W I}{R:W→ Rake.Label B}{Y:Rake.Dance G I W}
lemma stageable (hx:Mesh P x)(h:P.θ=0)(ht:∀ i, Cool.Fixed (x i))(hv:DOrd K P M R x Y)(s:Finset W): Stageable P ( plenum x Y s ):= by
    obtain hE:= sents hx h hv ht s; obtain hp:= aroma hx h hv ht s; refine ( sub_add_cancel (plenum x Y s) ( resin x Y s ) ) ▸ (fun n=> ?_); exact ( royalU ((hE n).known) ).add ( hp n ) -- ambiguity
abbrev Colorable (P:IntervalFamily I)(X:T ( Glade G I ))(d k:ℕ):= ∀ n<d, paidC P ( X n ) k
lemma field_whole (hx:Mesh P x)(h:P.θ=0)(ht:∀ i, Cool.Fixed (x i))
    (hv:DOrd K P M R x Y)(s:Finset W)(d k:ℕ):
    let F := plenum x Y s
    ∃ (p:Details B I k), Valid (Station P) p ∧
        ∃ Z, Response Z M P.η (-1) ∧ Reps Z 0 (Station P) ∧
            Colorable (Station P) ( F-Physical P.η M p-nav M P.η Z ) d k := by
    intro F
    obtain ⟨T,H,hP⟩:= convert_x liveS (safe_Ward hx h ht hv s)
        (fun i=> zero_book ( stageable hx h ht hv s i )) d k
    obtain ⟨p,hp,Z,hZ,hQ,hT⟩:= H
    rw [hT] at hP
    exact ⟨ p,hp,Z,hZ,hQ,(by rw [sub_sub]; exact hP.earlier ) ⟩

end YM.FVA2.O.Hue
