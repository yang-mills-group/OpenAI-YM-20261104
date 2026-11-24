import YM.RGComparison.Core16.Silk.Roll
/-!
# Taylor terms of a Glyph. Full tube support carries through Word requests; visualization
 Secondary atom derivative budgets from `Lumen.Spacing` paid in Aspiration instead of repeater overlap norm.
 Both steps on Cond.G kernel Hermann. No Taylor at varying `tilt` or altering Θ. Cost uniform at any β>0
 specified by uniform charter granted earlier; eventual fully rigorous on stationary Wick from assembly.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Silk
open Function Filter Lattice RG Tree Wilson MeasureTheory Metric Lumen Lumen.Planet Forge
open PertExtension PertExtension.Series Tested Radial
open Precision Finset
open scoped Topology ContDiff PowerSeries Classical BigOperators InnerProductSpace
variable {G:Gauge}{S:Side}{ι k T A D L I : Type}[Fintype ι][Fintype k][Fintype T][Fintype A][Fintype D][Fintype L]

variable {X:Shelf G A D} (P:Planet X S ι k T) (p:Stuff G ι L) (ψ:(L→G.Color)→ℝ)

-- Element map; roots. Need support & cardinal AND exact covariance multiplicative calculus,
-- not switching to differently priced norms along the proof (next nomination).
def field (p:Stuff G ι L) (i:Wire G L) : Rail G ι := match p i.1 with
   | .inl j=> [(j,i.2)]
   | .inr _=> []

def clip (p:Stuff G ι L)(i:Wire G L) : ℝ:= match p i.1 with
   | .inl _=> 1
   | .inr v=> v i.2
omit [Fintype ι] [Fintype L] in
lemma cluster (u:Wire G L)(g:ℝ)(x: Sky G ι) : tell p u g x=clip p u * sing (field p u) g x:=by
     unfold tell field book clip; rcases h:p u.1 with i|i
     · simp [sing,tally,curve,div_eq_mul_inv,mul_comm]
     simp [sing]

abbrev Wires (G:Gauge)(L:Type)(n:ℕ):= Fin n→Wire G L
variable {j n : ℕ}
variable (q:Wires G L n)

def weave (p:Stuff G ι L) (q:Wires G L n): Rail G ι:= (List.ofFn q).flatMap (field p)
def gauge (p:Stuff G ι L) (q:Wires G L n) : ℝ:= ∏ i, clip p (q i)

omit [Fintype ι] [Fintype L] in
lemma length_bound : (weave p q).length≤n:=by
   induction n with
   | zero=> simp [weave]
   | succ n H=> unfold weave; rw [List.ofFn_succ,List.flatMap_cons,List.length_append]
                have hf:(field p (q 0)).length≤1:= by unfold field; split <;> simp
                exact (Nat.add_le_add hf (H (Fin.tail q))).trans (le_of_eq (Nat.one_add ..))
omit [Fintype ι] [Fintype L] in
lemma seals (g:ℝ)(x:Sky G ι) : ∏ i,tell p (q i) g x = gauge p q * sing (weave p q) g x := by
   induction n with
   | zero=> simp [gauge,sing,weave]
   | succ n H=> unfold gauge weave; rw [Fin.prod_univ_succ,Fin.prod_univ_succ (fun i=> clip p (q i)),List.ofFn_succ,List.flatMap_cons,sing_join]; rw [cluster]; have h:=H (Fin.tail q); unfold Fin.tail at h; rw [h]; unfold gauge weave; ring

-- not Ring, take nth at the END of Entrance.
def warpPay (ψ:(L→G.Color)→ℝ) (q:Wires G L n):=YM.Tensor.coeff ψ n 0 (fun i=>one (q i))
def tagPrice (q: Wires G L n):= warpPay ψ q * gauge p q
def night (R : Rail G ι→Roll) (w:Rail G ι) (n:ℕ) : Roll:= ∑ i:Wires G L n,tagPrice p ψ i • R (weave p i++w)
def sight (w:Rail G ι) (f:Melody G ι)(g:ℝ) := P.expect g (sing w g*f g)

omit [Fintype ι] in
lemma tracing (n:ℕ) (g:ℝ)(x:Sky G ι) : tale p ψ n g x= ∑ i:Wires G L n, tagPrice p ψ i * sing (weave p i) g x:=by
    let U:= book p g x; let A : Wires G L n →ℝ := warpPay ψ
    change YM.Tensor.diagonal (YM.Tensor.coeff ψ n 0) U= _
    unfold YM.Tensor.diagonal; rw [show (fun _ : Fin n=> U)= (fun _=> ∑ i: Wire G L,tell p i g x • one i) from funext (fun i=> treasury (ι:=ι) p g x),(YM.Tensor.coeff ψ n 0).map_sum (α:=fun _=> Wire G L) (fun _ i=>tell p i g x • one i)]
    refine Finset.sum_congr rfl fun i _=>?_ ; unfold tagPrice; rw [(YM.Tensor.coeff ψ n 0).map_smul_univ (fun u: Fin n=>tell p (i u) g x), smul_eq_mul, Silk.seals (ι:=ι) p (i:Wires G L n)]; change _ * A _=A _*_*_; ring

variable (H:P.Steady)
include H
lemma solder (w:Rail G ι)(n:ℕ) : train (sight P w (tale p ψ n)) (night p ψ (price P) w n):= by
    refine (train.join (fun i=> (tagPrice p ψ i) • sway P (weave p i++w)) _ univ (fun i hi=> (supplies _ H).lift (tagPrice p ψ i))).travel ?_
    filter_upwards [Fk.tollLess (willing H.prices)] with g hg
    unfold sight; rw [show sing w g*tale p ψ n g= ∑ i:Wires G L n,(tagPrice p ψ i) • sing (weave p i++w) g from funext fun x=> ?_]; swap
    · rw [Pi.mul_apply,tracing]; rw [mul_sum,Finset.sum_apply]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [Pi.smul_apply,sing_join,smul_eq_mul]; ring
    rw [paid H hg _ (fun i:Wires G L n=> tagPrice p ψ i • sing (weave p i++w) g) (fun i _=> (Envelope.const _).mul (havenreal (sing_cont ..))),Finset.sum_apply]; simp_rw [Planet.expect_mul]; rfl

end YM.RGComparison.Core16.Silk
