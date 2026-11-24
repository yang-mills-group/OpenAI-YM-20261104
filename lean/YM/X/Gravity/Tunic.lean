import YM.X.Gravity.Peace
/-! # tint-ℒ on Curly. -/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Gravity
open Lattice Wilson Next.Rank Normal Interval PertExtension LatticePT Filter Set Function Metric MeasureTheory Asymptotics Reed Size Braid
open MvPolynomial Hinge Clove Haze Grow Shelf Ocean Fielding Crystal Perch LiftMark
open Stems hiding X
open scoped Topology ContDiff BigOperators Classical
variable {q: ℕ+}(hq:1<q.val){V:Type*}{m n d l:ℕ}{G:Gauge}{R r:ℝ}
variable (t:G.El)(k:Side)
local notation "Cp"=>tonal t
local notation "Q"=>flow G k
lemma tintedM (p:Curly G): milk Q (tonal t p)= Cp (milk Q p):= by unfold tonal; rw [prepared,color_scope]
lemma tintedMinus (p:Curly G): milk (-Q) (tonal t p)= Cp (milk (-Q) p):= by nth_rw 1 [← miles Q p]; rw [← tintedM t k, minus Q]
lemma tonal_hit (p s:Curly G): hit Q (Cp p) (Cp s)= Cp (hit Q p s):= by
   have h(i:Hair G): hit Q (tonal t p) (tonal t (X i))=tonal t (hit Q p (X i)):= by
      unfold tonal; rw [exchange_x, hit_glyph,edge,exchange_slit,hit_point]; rw [← show (scope (robe t) Q).cov i=(flow G k).cov i from congr_fun (congr_arg Symmetric.cov (color_scope t k)) i]; rfl
   induction s using MvPolynomial.induction_on with
   | C a=> rw [show tonal t (C a)=C a from (tonal t).commutes _]; simp only [hit_c,map_zero]
   | add a b x y=>simp only [map_add,x,y]
   | mul_X p i ih=> rw [map_mul,Derivation.leibniz,Derivation.leibniz,map_add]; simp only [smul_eq_mul,map_mul,h i];rw [ih]
lemma tonal_k (p s:Curly G): knot Q (Cp p) (Cp s)= Cp (knot Q p s):= by unfold knot; rw [tintedMinus,tintedMinus,← map_mul,tintedM]
lemma tonal_M (p s:Curly G): multi Q (Cp p) (Cp s)= Cp (multi Q p s):= by unfold multi; rw [map_sub,map_sub, tonal_k,map_mul,tonal_hit]
lemma mark_n {f:CoverConfig G→ℝ}(h: GaugeInvariant f)(hp:ProjectorNext.Calibration.Small G f): tonal t (mark f hp d)=mark f hp d:=by apply snap_ext; intro A; rw [tonal_eval,mark_test,mark_test,along_fixed t h]
lemma book_n (P:Word G)(i:ℕ) : tonal t (bookMark P i)=bookMark P i:= by rw [bookMark,map_sum]; refine Finset.sum_congr rfl (fun b _=>?_); rw [map_smul]; exact congr_arg _ (mark_n t (fun s x=>congr_arg Complex.re (P.sound.gaugeInvariant (Pi.single b 1) s x)) (opt b P.sound P.chosen))
lemma warp_s (χ:Lane): tonal t (fireMask (G:=G) χ)=fireMask χ:=by
    let L:=(tonal t).toLinearMap.restrictScalars ℝ; let f(x:Cover):=∑ i:PlaqAxes, flashVertex (G:=G) (x,i); change L (beadR χ f) = beadR χ f; rw [beadLm]; refine congr_arg _ (funext fun i=>?_); unfold f; rw [comp_apply,map_sum]; exact Finset.sum_congr rfl (fun j _=> mark_n t (f:= Log.flame (i,j)) (fun s U=> by rw [Log.flame,face_gauge,G.price_conj]; rfl) (Log.brief _))
lemma warp_tonal (P:Word G)(φ:Floor R)(k:ℕ) : tonal t (warp q P φ k)= warp q P φ k:= by unfold warp crisp;rw [map_sub,←tonal_M,←tintedM,←tintedM,warp_s, book_n,book_n]
lemma atmospheric (P:Word G)(φ:Floor R) : watch G P.d (exposed q P φ m) ∈ physicalJet G P.d:= by
    apply flop_jet (exposed q P φ m); exact pigment_touched (fun x A=>by rw [← tonal_eval x A (warp q P φ m), warp_tonal]) P.d -- type unification flop implicit
end YM.PositionX.Gravity
