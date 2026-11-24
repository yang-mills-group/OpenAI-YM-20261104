import YM.MS.Puff.State
import YM.MS.Puff.Story
/-!
Scalar peripheral channel. Exponent converting to moments obeys all compact-index limits.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Puff.Mom
open Set Filter Function Finset Metric MeasureTheory Real
open Koszul Plane Flux Wire Book Convolve Orbit Cog Orbit.LogReal
open SplitP Actors Engine Dynamics HeatFlow
open scoped Topology ContDiff Interval
variable {A W I J E:Type}{p:Sector A}[LinearOrder W]{F B Z:Series A}{L:Lines A}{s:Finset W}
   {Q:SpecB A}{X: Infos W A}{P:Mate A W}
def lampL (A:Type)(t:ℝ): Linear ( OM A ) ℂ:= (LinearMap.proj (R:=ℂ) (i:= [])) ∘ₗ (LinearMap.proj (R:=ℂ) t) -- fix
lemma testing (t:ℝ): Tether (lampL A t) (Pie p) Toy:= ⟨ rfl, fun _ _=> times_nil .. ⟩
lemma moments_0 (V:Infos W A)(t:ℝ)(n:ℕ)(s:Finset W): Mez p V s n t []= bouquet (fun i j=> V i j t []) s n:= congr_fun ((( testing (p:=p) t ).Extrapolation useN).figure (marked W) V s) n
-- general use for limit of regulator as well as Θ limits
variable {l:Filter I}{u:I→ Finset W→ T ℂ} {v:Finset W→ T ℂ}
def align (l:Filter I){J:Type}(u:I→J→ℂ)(v:J→ℂ): Prop:=∀ i:J,Tendsto (fun p=> u p i) l (𝓝 (v i))
def Accord (l:Filter I)(u:I→ Finset W→ T ℂ)(v: Finset W→ T ℂ): Prop:=∀ i:Finset W,align l (fun t=> u t i) (v i)
namespace Accord
variable {f g:I→Finset W→ T ℂ} {h:Finset W→ T ℂ}
lemma product (hF: Accord l f v)(hx: Accord l g h): let P:= (Trunk.stack (marked W)).core; Accord l (fun i=> P ( f i ) ( g i )) (P v h):= by
    intro P i j; change Tendsto (fun p=>( ∑ d∈ subs i,Trunk.core ( f p d.1 ) ( g p d.2 )) j) l (𝓝 ((∑ d∈subs i, Trunk.core ( v d.1 ) ( h d.2 )) j )); simp_rw [Finset.sum_apply]; exact tendsto_finsetSum _ (fun d _=> tendsto_finsetSum (antidiagonal j) ( fun p _=> ( hF d.1 p.1 ).mul ( hx d.2 p.2 ) )) -- ambiguity finite complex mult LP.Trunk
lemma power (hf: Accord l f v)(k:ℕ): let P:= Trunk.stack (marked W); Accord l (fun i=> P.power (f i) k) ( P.power v k ):= by induction k with| zero=> intro P i j; exact tendsto_const_nhds| succ k ih=> exact product hf ih
lemma select (hf:Accord l f v)(i:Finset W)(j:ℕ): Tendsto (fun p=>bouquet (f p) i j) l (𝓝 (bouquet v i j)):= by
    unfold bouquet Cheer Actors.cheers; simp_rw [ Finset.sum_apply ]; exact tendsto_finsetSum _ (fun x _=> (power hf x i j).const_smul ( Actors.phase x ))
end Accord
lemma momDepart {X:Infos W A}{p:Sector A}(h:∀ w n,Tendsto (fun t:ℝ=> X w n t []) atTop (𝓝 (v w n)))(s:Finset W)(n:ℕ): Tendsto (fun t:ℝ=> Mez p X s n t []) atTop (𝓝 (bouquet v s n)):= by
    have he : Accord atTop (fun t i n=> X i n t [] ) v := h; apply ( he.select s n ).congr fun p=> Eq.symm ?_; exact moments_0 ..
end YM.MS.Puff.Mom
