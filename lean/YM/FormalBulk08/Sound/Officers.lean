import YM.FormalBulk08.Sound.Rebase
import YM.FormalBulk08.Drift.Evolve

set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Sound
open Lattice Laurent Bloch RG Precision Wilson Orb Reef City Filter Function Series Wick Jets Stationary Lotus Shore Lava Gorge Mesa Cork Wine Flat Glide Bank Work.F08 Next.Free Chapel Rift Aster Dove Dove.Lab PowerSeries UVExtension UVExtension.Free Matrix Exterior Tree North
open Dawn Kemp Drift Quire Elm Pose
open scoped Topology ENNReal BigOperators Classical Matrix ContDiff
variable {G:Gauge}{I J: Type}{K:KernelChoices}{ρ:ChartRatio G}{W:Lab G K I}{E d j t e r D:ℕ}
variable (x:Leaf W.scrolls)(a:hue G)(o:Loc G 1)(hp:Use W ρ E) (h:LocalRatio ρ)(hs:G.Simple)
variable (n:Side)
abbrev Shaw (T:Pot G)(l:ℕ) := Reef.seat (rug x n) (Kemp.banner l T (n*(W.pat x).L))
def Mastodon (T:Pot G)(l:ℕ):= joust (zeta x n) (lever (hospital x n hp) (Shaw (W:=W) x n T l))
lemma passport (T:Pot G)(l)(h:Young T l)(ht:∀ e r,Agate (T e r))(e r:ℕ):
    rancho (Mastodon x hp n T l) e r= pearl ((limY x).acts n) (pearl ((pane G (W.pat x) (W.wood x.a x.b)).acts n) (pearl ((winging (Rim G (W.pat x)) (Loc G 1)).acts n) (sieve n (altitude (W.pat x) T e r)))) := by
    let S:=boxS x n; let P:= Kemp.banner l T (n*(W.pat x).L)
    rw [Mastodon,turned]; apply (rename_income _ _ e r).trans; apply congr_arg
    rw [show rancho (joust (zeta x n) _) _ _ = _ from tor_yolk S (W.wood x.a x.b) P e r]; congr 1
    apply congr_arg; rw [show rancho P e r=_ from badge T h ht le_rfl _ e r]; exact (rinse _ (T e r) S.ratio).symm -- congr
lemma monochrome (T:Pot G)(l)(h:Young T l)(ht:∀ e r,Agate (T e r)): Young (rancho (lever (hospital x n hp) (Shaw x n T l))) l:= by
    intro e r he; refine h _ _ (fun hv=>?_); apply he; refine (Bank.quake _ (zeta x n) e r).mpr ((passport x hp n T l h ht e r).trans ?_); unfold altitude;rw [hv,jetty_zero,sieve_zero,pearl_zero,pearl_zero,pearl_zero]
lemma support_flag (V T: Pot G)(l :ℕ)(k:(boxS x n).Choices)(h:LocalRatio ρ)(hm:Young T l)(ha:∀ e r,Agate (T e r))(hs:Vivid V)(hU:Solved (hospital x n hp) (joy (ρ:=ρ) x n V k)):
    rancho (flag (hospital x n hp) (joy (ρ:=ρ) x n V k) (Shaw x n T l)) e r= ∑ i∈Finset.range (l+3*e+1), jetty (coastRight _ _ _) (dipper ((limG x).acts n) (swim ((limG x).acts n) (rancho (harvestF x n hp V k))) (rancho (Mastodon x hp n T l)) i e r):= by
   let F:=hospital x n hp; let Q:=zeta x n;let Z:= joy (ρ:=ρ) x n V k;let A:=rancho (cobalt F Z);let B:=rancho (harvestF x n hp V k);let Y:=Shaw x n T l
   let M:=rancho (lever F Y)
   have hA : ∀ a b,A a b=jetty Q (B a b):= fun a b=> infer_joust Q _ _ _
   have hF: Fiery A:=fun i j he=> wealth x n hp V hs k h _ _ fun hz=> he ((Bank.quake (cobalt F Z) _ _ _).mpr hz)
   let p:=aqua F.saddle (I:=wire G n); let U:= (limG x).acts n; let q:= rancho (Mastodon x hp n T l); have hu:= swarm x n hp; have he:∀ i j k, swim p A i j k=jetty Q (swim U B i j k):=fun i j k=> (dye_swim Q p U hu B A hA i j k).symm
   rw [show rancho _ _ _= _ from extraction_mark F Z Y hU hF (monochrome x hp n T l hm ha) _ _ (l+3*e) (by omega)]; apply Finset.sum_congr rfl; intro i hi; rw [← show jetty Q (dipper U (swim U B) q i e r)=_ from dye_dip Q p U hu (swim U B) q (swim p A) M he (fun i j=>infer_joust Q (lever F Y) i j) i e r]; rfl
lemma certify (T U:Pot G)(g:Vivid T)(hg:Young U d)(hz:∀ i j,Agate (U i j))(hG:∀ i j,∃ B:ℝ,Bail (fame _) (W.windowU x) (T i j) B)(p:LocalRatio ρ)(y:edgeL G)(k:(n:Side)→(boxS x n).Choices)(pU:∀ i j,∃ B, Knoxville (fame _) (W.windowU x) y (U i j) B)(i j t:ℕ):
   let X:=(Bank.scroll (W.pat x).L _ y).1
   Kalm (W.windowD x) (coastRight _ _ _ (X,o)) (dipper (lands (limG x)) (swim (lands (limG x)) (camp ρ x T)) (fun e r=> liftHat x (U e r)) i j t) (fun n=> dipper ((limG x).acts n) (swim ((limG x).acts n) (rancho (harvestF x n hp T (k n)))) (rancho (Mastodon x hp n U d)) i j t):= by
   intro Z
   have ht :=(layers_price x hp).1; let s:= W.windowD x; have hs':0<s:=hp.zero x
   have H(n:Side):Grate (lake n _) s ((limG x).acts n) ((Fintype.card (BoardL G (W.pat x) (W.wood x.a x.b)))* W.callL x ρ E):= by
      have he:=trundle n (limG x) ht (W.turn_whose hp x).plus.le hs'.le; refine ⟨he.costs,fun i=>?_⟩; have hu:=he.rows i; simp_rw [rinkshine,skit_sub n _ i.1] at hu; exact hu
   let R:=limG x; have hy:= landing_row R (Row.rights _ _ ht hs'.le); have hv(a b)(hv:0<b):= arose_curve x hp k g p (hG a b).choose_spec (⟨0,hv⟩:Fin b); have he:= kith_swim hy _ hs' (Eventually.of_forall H) (fun n=>pastured x n hp) hv
   refine kalm_group _ _ _ t _ _ (fun u w q _ _ hq=> he u w q hq) ?_ le_rfl hy hs' (.of_forall H) (fun n=>pastured x n hp)
   intro e r _; simp_rw [passport x hp _ U d hg hz]; let P:=W.pat x;let Q:=Bank.scroll P.L (Loc G 1) y; obtain ⟨B,hB⟩:= pU e r
   have hx:=sieve_kalm _ (rinse_bill (U e r) P.L (W.turn_whose hp x).ship hs'.le Q (show Knoxville (fame (Loc G 1)) (W.windowU x) ((Bank.scroll P.L _).symm Q) (U e r) B from (by unfold Q; rw [Equiv.symm_apply_apply];exact hB))) hs'.le
   have hp':=kalm_stream (R:=winging (Bank.Rim G P) (Loc G 1)) (Sum.inr o) (wing_strip s) zero_le_one hs' hx; have hu:=kalm_stream (R:=pane G P (W.wood x.a x.b)) (Sum.inr o) (pane_pay _ s) zero_le_one hs' hp'; have hq:= kalm_stream (R:=limY x) (Sum.inr o) (layers_price x hp).2 (zero_le_one.trans (le_max_left ..)) hs' hu; unfold altitude liftHat; exact hq
end YM.FormalBulk08.Sound
