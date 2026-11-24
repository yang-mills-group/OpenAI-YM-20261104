import YM.Comparison.RG02.Bare.Flat
/-!
# No holes at a flat connection, even with torus holonomy

 Prediction law uses the actual arms with one common patch. Flatness on cover suffices to
 show ideal predictor sees exactly the long Wilson lines *through anchors*. Allows continuity for
 this exact choice at such fields, at fixed regulator; no claim near arbitrary seams. -/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Bare
open Function Filter Finset MeasureTheory Lattice Wilson RG Pressure
open scoped Classical Topology BigOperators Matrix.Norms.Frobenius ContDiff
variable {c f : Side} {G : Gauge} {U : Config G f}
variable (S : StepData c f) (h : Flat U)
local notation "P"=> S.patch
local notation "K"=> S.kernel
variable (x : Site c) (l m : Lattice.Order)
local notation "o"=> S.ratio.embed x
local notation "U₁"=> expandAt (o) U
local notation "h'"=> S.patch.axial (expandAt (o) U) (S.patch.center,l)
include h
private lemma turn (a b : Walk) (x y : Cover) (z : Site f) (he : stop x a=y) (hy : stop x b=y): travel (expandAt z U) x a=travel (expandAt z U) x b:= by rw [travel_at,travel_at]; exact journey h a b _ (add_left_cancel (( (summit x a).symm.trans he).trans ((summit x b).symm.trans hy).symm))
private lemma flatVia (i j : S.patch.Points): (P).via (h') (U₁) i j m=1:= by
   have hs : travel (U₁) 0 (route 0 i.val l)*travel (U₁) i.val (route i.val j.val m)=travel (U₁) 0 (route 0 j.val l):= by
      have he:= turn h (route 0 i.val l ++ route i.val j.val m) (route 0 j.val l) 0 j.val o (by rw [stop_append,route_end, route_end]) (route_end ..); rwa [travel_append,route_end] at he
   change travel (U₁) 0 (route 0 i.val l)*travel (U₁) i.val (route i.val j.val m) * (travel (U₁) 0 (route 0 j.val l))⁻¹=_; rw [hs,mul_inv_cancel]

lemma seesMin : (P).usesMin K U₁ := by
   intro l m i j; rw [flatVia S h]; exact (G.chord_one.symm ▸ (K).frame_cut_pos)
variable (ht : S.patch.Branches S.kernel G)
omit h in
private lemma score_positive (H : S.patch.Frame G) : 0 ≤ (P).score U₁ H:=by unfold Patch.score Patch.average; exact mul_nonneg (by positivity) (sum_nonneg fun x _=> mul_nonneg (by positivity) (sum_nonneg fun y _=> mul_nonneg (by positivity) (sum_nonneg fun _ _=> (G.price_range _).1)))
include ht
lemma flat_frame (T : S.SitesChoice) : S.frames U T x=h' := by
   unfold StepData.frames Patch.frame; rw [if_pos (seesMin S h x)]
   apply (ht.frame_unique U₁ (seesMin S h x)).unique (((P).min_exists U₁).choose_spec)
   have hs : (h') ((P).center)= travel (U₁) 0 [] := turn h _ _ _ _ (o) (route_end ..) rfl
   constructor
   · exact hs
   intro W _; unfold Patch.score; simp_rw [flatVia S h x]; simp only [G.price_one, Patch.average, Finset.sum_const_zero,mul_zero]; exact score_positive S x W

def ground (U : Config G f) (e : Edge (Site c)) := travel U (S.ratio.embed e.1) (S.repath e.2)
lemma flat_connector (T : S.SitesChoice) (x : Site c) (e : Axis) : S.connector U T (x,e)=Function.const _ (ground S U (x,e)) := by
   funext i
   rw [StepData.connector,flat_frame S h x 1 ht T, flat_frame S h (x+step e) 1 ht T]
   unfold Patch.axial; simp_rw [travel_at,Patch.center, map_zero, zero_add]
   let a := x+step e; let p:=route 0 i.val 1; let q:=S.repath e
   let E := S.ratio.embed a
   let w:= travel U (S.ratio.embed x) p; let w':= travel U E p
   let B:= wrap f i.val
   let v':= travel U (B+(S.ratio.embed x)) q; let v:=travel U (S.ratio.embed x) q
   have he : pathLength p=i.val := by rw [← zero_add (pathLength _),← summit,route_end]
   have hh := journey h (p++q) (q++p) (S.ratio.embed x) (by rw [← zero_add (pathLength (p++q)),← zero_add (pathLength (q++p)),← summit,← summit,stop_append,stop_append]; simp_rw [summit,add_assoc, zero_add]; rw [add_comm])
   have hp : stop (S.ratio.embed x) q=E:=Eq.trans (S.stop_repath ..) (S.leap ..).symm
   rw [travel_append,travel_append, hp, target (S.ratio.embed x) p, he,add_comm (S.ratio.embed x)] at hh
   change w*v'*(w')⁻¹=v; change w*v'=v*w' at hh; rw [hh,mul_inv_cancel_right]

variable (e : Edge (Site c)) (T : S.Choices)
omit h ht in
private lemma constant_best (u : G.El) : S.patch.bondCost (Function.const _ u) u=0 := by unfold Patch.bondCost; simp
omit h in
private lemma best (u : G.El) : S.patch.best (Function.const _ u) = u := by
   let f := Function.const ((P).Points) u
   have hs : (P).usesBest K f:= lt_of_le_of_lt (((P).bond_min f).choose_spec u) ((constant_best S u).symm ▸ (K).predictor_cut_pos)
   exact (ht.predictor_unique f hs).unique (((P).bond_min f).choose_spec) (show ∀ v, (P).bondCost f u ≤ (P).bondCost f v from fun v=> by unfold f; rw [constant_best]; exact (sum_nonneg fun i _=> mul_nonneg ((P).weight_nonneg i) (G.price_range _).1))
lemma seesBest : (P).usesBest K (S.connector U T.1 e) := by
   cases e with | mk x e => rw [flat_connector S h ht]; unfold Patch.usesBest; rw [best S ht,constant_best]; exact (K).predictor_cut_pos
lemma prophecy : S.prediction U T e=ground S U e:= by
   unfold StepData.prediction Patch.predict; rw [if_pos (seesBest S h ht e T)]; cases e with | mk x e=> rw [flat_connector S h ht,best S ht]

lemma foretells : ContinuousAt (fun W:Config G f=> S.prediction W T) U := by
   let p := P
   have hE x : Continuous (fun u:Config G f=> expandAt (S.ratio.embed x) u) := by unfold expandAt; fun_prop
   have hp x : ContinuousAt (fun u: Config G f=> S.frames u T.1 x) U := by
       unfold StepData.frames Patch.frame; let Φ:=fun u:Config G f=> expandAt (S.ratio.embed x) u
       let s := {v:CoverConfig G| p.usesMin K v}
       have hu: s ∈ 𝓝 (Φ U):= p.min_open.mem_nhds (seesMin S h x)
       refine (((p.selected_cont ht _ (show Φ U∈s from seesMin S h x)).continuousAt hu).comp (hE x).continuousAt).congr ?_
       filter_upwards [(hE x).continuousAt.tendsto.eventually hu] with y hy; exact (if_pos hy).symm
   refine continuousAt_pi.mpr fun e=> ?_
   let B:=fun W:Config G f=> S.connector W T.1 e; have hB : ContinuousAt B U:=continuousAt_pi.mpr fun i=> ((continuousAt_pi.mp (hp e.1) i).mul ((continuous_travel _ _).continuousAt.comp (hE _).continuousAt)).mul (continuousAt_pi.mp (hp _) i).inv
   let q := {x:(P).Connector G | p.usesBest K x}; have hQ: q∈𝓝 (B U):= p.best_open.mem_nhds (seesBest S h ht e T)
   apply ContinuousAt.congr ((((p.best_cont ht) (B U) (show B U∈q from seesBest S h ht e T)).continuousAt hQ).comp hB)
   filter_upwards [hB.tendsto.eventually hQ] with y hy; exact (if_pos hy).symm -- maybe ContinuousAt.congr direction
end YM.Comparison.RG02.Bare
