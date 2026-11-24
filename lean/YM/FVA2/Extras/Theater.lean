import YM.FVA2.Extras.Align
/-! # Apply `merge` with exteriors at the specified positions

Auxiliary to `YM/FVA2/Extras/Result.lean`. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Extras
open MS Function Filter Set Finset MS.Latch Job MS.Plane MeasureTheory Real Metric
open Heat LogTime IntervalFamily Koszul Tone Momentum Landau Fiddle Osc Snap Wire Signal O
open O.Lives MS.City MS.Rake O.Tune Flux Book Convolve O.Serve O.Pad Vane High Detect O.Ward
open MS.Local.Physical MS.Land Outlook Rough Emit
open scoped Topology ContDiff Interval BigOperators
open Job.Belt Rake.Geo O.Hue O.Fuse O.Cool

variable {I Gv W: Type}[LinearOrder W] {G:Gauge}{b d:ℤ}{B:Deck G}{K:Booked B}{M:MS_Data G K}{P:Geo I}{x:Position W I}{Q:W→T (Glade G I)}{S:Finset W}{X:Rake.Dance G I W}
def note (x:Position W I)(Q:W→T (Glade G I))(i:W): Cart G I:= (x i,Q i)
variable {s t:Finset W}{L:List W}{i j:W} (H:Teams P M Q x X) (hW:Survey P M Q x)(hs:Mesh P x)
open Puff Puff.Actors
include H
lemma solo : untap x X {i}= swing G (x i) (Q i):= by unfold untap; rw [ H.2.1 ]; simp [rootX]
-- peel.Rake arbitrary enumerations
include hW hs
lemma resin_frame (h:L.Nodup) (hi:i∉L): merge G I ( L.map (note x Q)) ( note x Q i )= resin x X (insert i L.toFinset):= by
    have hp(v:Finset W)(y:W)(ht:y∉ v): resin x X (insert y v) = bond G I (swing G ( x y ) (Q y )) (resin x X v) := by rw [resin,raw_wax (X:=untap x X) ( fun s k=> bankTilt ( units hW H (fun i n=>calls hW hs H n i) k )) ht, solo H ]
    induction L with
    | nil=> unfold merge; rw [List.toFinset_nil,hp _ _ (notMem_empty _),resin_nil]; exact Eq.symm ( (glaze G I).identityR _ )
    | cons j L IH=> obtain ⟨ he,hD⟩:=List.nodup_cons.mp h; rw [List.toFinset_cons,Finset.insert_comm,hp _ _ ?_,List.map_cons,merge,IH hD (fun h=>hi (List.mem_cons_of_mem _ h)) ]; rfl
                    exact fun hv=> Finset.mem_insert.mp hv|>.elim (fun e=> hi (by simp [e])) (fun e=> he ( List.mem_toFinset.mp e ))
lemma scene (h:P.θ=0)(hd:L.Nodup)(hi:i∉L): Lucent P M 0 ( plenum x X (insert i L.toFinset) ) ( merge G I (L.map (note x Q)) (note x Q i) ):= by rw [resin_frame H hW hs hd hi]; exact ⟨ plates hW H (fun i n=> calls hW hs H n i) _, aligns hW hs h H _ ⟩
omit H
omit [LinearOrder W] in
lemma apart_scene (h:L.Nodup)(hi:i∉L): Scriven P M (note x Q i) (L.map (note x Q)) 0:= by
    refine ⟨ hW i,?_,?_,(List.pairwise_map).2 ( List.Pairwise.imp ?_ h ) ⟩
    · intro v hin; obtain ⟨i,hi,rfl⟩:= List.mem_map.mp hin; exact hW _
    · intro v hin; obtain ⟨j,hj,rfl⟩:= List.mem_map.mp hin; exact hs j i fun e=> hi (e ▸ hj)
    exact fun {a b} h=> hs a b h
include H
-- reconnect to separated exact MS extension for these fields. independent.All k/l.
abbrev reported (x:Position W I)(X:Rake.Dance G I W)(i:I)(s:Finset W)(n:ℕ): ℂ:= blade ( plenum x X s n ) i
lemma evaluate_full (i:I)(s:Finset W)(n:ℕ): Tendsto (fun t:ℝ=> Puff.Mom.bouquet ( fun k j=> X k j i t [] ) s n) atTop (𝓝 (reported x X i s n)):= by
    simp_rw [ ← sunrise ( x:=x ) ]; exact total_peak ( plates hW H (fun i n=> calls hW hs H n i) _ ) i n
end YM.FVA2.Extras
