import YM.MatchingLedger.Compass.Sea

/-! # Uniqueness of the independent comparator on its covered cost/calendar.
No loss with depth. Port from programming API. -/
set_option autoImplicit false
noncomputable section
namespace YM.MatchingLedger.Compass
open Function Filter Set MeasureTheory Precision RG Tree Wilson Lattice Work Exterior
open WilsonStartup.Change Extension.UV.LoopRate Extension.UV.StationaryData Bid
open scoped ContDiff Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {A:Levels G}{N m:ℕ}{U V:Crop A}{C C':ChartRatio G} (ht:LocalRatio C)
local notation "D" p=>A.S.side m p
variable (hA:Supply.AsDivisors A.S) (hx:m<N) (hU: U.Fires C) (hV: V.Fires C)
   (h : ∀ p, Stunning (A.params (m+1)).clip (A.S.side (m+1) p) (U.model N (m+1)) (V.model N (m+1)))

open Lines Mirrors
include hA hx hU hV ht h
variable (hG:G.Simple)
lemma equal_windows (W₀:Nontrivial G.Color) : U.alpha N m=V.alpha N m:=by
   obtain ⟨e,he⟩:= exists_norm_eq G.Color (c:=1) zero_le_one
   have heq (q:ℕ) : fee (D q) (A.params m).clip (U.model N m) (U.alpha N m) e= fee (D q) (A.params m).clip (V.model N m) (V.alpha N m) e:= by unfold fee; rw [show H₂ (draft (c:=D q) (U.alpha N m) (U.model N m) (A.params m).clip)=H₂ (draft (c:=D q) (V.alpha N m) (V.model N m) (A.params m).clip) from uniform_draft ht hA hx hU hV h q]
   obtain ⟨_,_,_,hu⟩:= hU.budget N m hx.le; obtain ⟨_,_,_,hv⟩:= hV.budget N m hx.le
   exact tendsto_nhds_unique_of_eventuallyEq (payout hu _ A m e he) (payout hv _ A m e he) (Eventually.of_forall heq)
lemma equal_loop (W₀:Nontrivial G.Color) (p':ℕ) : Stunning (A.params m).clip (D p') (U.model N m) (V.model N m):=by
   let n:= D p'; obtain ⟨F⟩:= Tree.select ((A.clock.op m p').ratio) (A.clock.op m p').patch.odd_side
   obtain ⟨_,_,_,_,hv,_,hw⟩:=hU.each N m hx
   obtain ⟨_,_,_,_,_,_,hh⟩:=hV.each N m hx
   have hy:= hw p' F; have hz:= hh p' F
   have he:=drops F (Classical.arbitrary (A.clock.op m p').Choices) hy.2.1 hz.2.1 (h p').classicalEq hv hy.1 hy.2.2.1 hz.2.2.1
   obtain ⟨_,_,_,ht₁⟩:= hU.budget N m hx.le; obtain ⟨_,_,_,ht₂⟩:= hV.budget N m hx.le
   have hn:Matches 1 (L n (U.model N m)) (L n (V.model N m)) 0:= (rooted _ (f:=n) _ ⟨_,_,_,ht₁⟩).2.trans (rooted _ (f:=n) _ ⟨_,_,_,ht₂⟩).2.symm
   refine ⟨he,hn.left,hn.right,fun i hi=>?_⟩
   by_cases h₁:i≤1
   · exact hn.jets _ h₁
   rw [show i=2 by omega]
   let σ:= U.alpha N m; let β:= V.alpha N m; let W:= U.model N m; let Q:= V.model N m; let p:= (A.params m).clip
   have hH : H₂ (full (n:=n) W p σ)= H₂ (full Q p β):= ((sees ht₁ σ).jets 2 le_rfl).trans ((uniform_draft ht hA hx hU hV h p').trans ((sees ht₂ β).jets 2 le_rfl).symm)
   rw [show β=σ from (equal_windows ht hA hx hU hV h W₀).symm] at hH
   let f(H:PathData G):= σ • AT n p H
   have hM:= he.refl_comp (u:=fun a:ℝ=>σ*a) (contDiffAt_const.mul contDiffAt_id)
   change iteratedFDeriv ℝ 2 (f W+L n W) 0=iteratedFDeriv ℝ 2 (f Q + L n Q) 0 at hH
   have hx : Matches 4 (f W) (f Q) 0:= hM
   rw [iteratedFDeriv_add_apply (hx.left.of_le le_top) (hn.left.of_le le_top), iteratedFDeriv_add_apply (hx.right.of_le le_top) (hn.right.of_le le_top),hx.jets 2 (by decide)] at hH
   exact add_left_cancel hH
omit hx h
lemma along (W₀:Nontrivial G.Color) (hx:m≤N): ∀ p, Stunning (A.params m).clip (D p) (U.model N m) (V.model N m):=by
  induction hx using Nat.decreasingInduction with
  | self=> exact fun p=> ⟨(hU.summit N p).trans (hV.summit N p).symm,(hU.atLoop N p).trans (hV.atLoop N p).symm⟩
  | of_succ k hk ih=> exact equal_loop ht hA hk hU hV ih W₀

-- specialize with ANY witness(es). No naming equality.
include hA in
lemma concordant (W₀: Nontrivial G.Color) : U.harvest=V.harvest:=by
   unfold Crop.harvest; congr! 1
   · funext N m p i; split_ifs with he; exact (along ht hA hU hV W₀ he.2 p).classicalEq.jets _ he.1; rfl
   · funext N m p; split_ifs with he; exact (along ht hA hU hV W₀ he p).loop.jets _ le_rfl; rfl
   funext N m; split_ifs with he; exact equal_windows ht hA he hU hV (along ht hA hU hV W₀ (Nat.succ_le_of_lt he)) W₀; rfl
omit ht hU hV hA in
theorem standard (G:Gauge) {A:Levels G} (hA:Supply.AsDivisors A.S)(hG: G.Simple) : ∀ U V: Harvest A, Reaps A U → Reaps A V → U=V:=by
   intro U V h g
   obtain ⟨C',hc,Q,hQ,rfl⟩:=h; obtain ⟨Z,hz,F,hF,rfl⟩:= g; exact concordant hc hA hQ (F.compatible hF hz hc) hG.nontrivial_color
end YM.MatchingLedger.Compass
