import YM.OPE.Compatible.Straws.Thole
/-!
# Jet calculus along small paths of coarse parameters
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra
open Function Filter Set Lattice Laurent Tree Woody Weir Cascade MeasureTheory LinearMap Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff ENNReal Matrix.Norms.Frobenius
open PertExtension Series GaussianScore Asymptotics Precision
variable {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
local notation "Lf" => Tested.germ
open Radial ScriptJ JetS
namespace Stranded
open Flock
variable [FiniteDimensional ℝ E]
lemma nit {ι:Type} (s:Finset ι)(p:ι→ℝ→ℝ)(k:ι→Token)(hp:∀ i∈s,Reads (p i) (k i)): Reads (∑ i∈s,p i) (∑ i∈s,k i):=by induction s using Finset.induction_on with
   | empty=> simp only [Finset.sum_empty]; exact Reads.constants 0
   | insert i s hi ih=> rw [Finset.sum_insert hi,Finset.sum_insert hi]; exact (hp _ (by simp)).sum (ih fun j hj=> hp _ (Finset.mem_insert_of_mem hj))
lemma nitP {ι:Type} (s:Finset ι)(p:ι→ℝ): (∑ i∈s,(⟨0,0,p i⟩:Token))=⟨0,0,∑ i∈s,p i⟩:=by induction s using Finset.induction_on with
   | empty=>simp; rfl
   | insert i s hi ih=> rw [Finset.sum_insert hi,Finset.sum_insert hi,ih]; apply JetS.eta<;>simp
variable (L:Law E)
private lemma hush {p:ℝ→E}{a b:E}(q: Dual ℝ E)(h:Reads p ⟨(0:E),a,b⟩): Reads (fun i=> q (p i)) ⟨0,q a,q b⟩:=by
    rw [←map_zero q]; exact h.tours (toContinuousLinearMap q)
lemma arb {a b:E} (p:ℝ→E)(h: Reads p ⟨0,a,b⟩): Reads (fun i=>L.P (p i) (p i)) ⟨0,0,L.P a a⟩:=by
    let k:= Module.finBasis ℝ E; let f(i:Fin (finrank ℝ E)):= k.coord i; let V(x:E):=L.P x x; let Q(i j): ℝ→ℝ:= fun t=> f i (p t)* L.P (k j) (p t); let S(i j):= f i a* L.P (k j) a
    have ht(x:E): V x=∑ i, f i x * L.P (k i) x:=by
        unfold V; nth_rw 1 [show x=∑ i,f i x • k i from (k.sum_repr _).symm]; simp only [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul]
    have hp(i j): Reads (Q i j) ⟨0,0,S i j⟩:=by
        let s:=L.P (k j); convert (hush (f i) h).pile (hush s h) using 1
        · rfl
        apply JetS.eta <;> simp; rfl
    change Reads (fun i=>V (p i)) ⟨0,0,V a⟩; rw [show (fun i=>V (p i))= (∑ i,Q i i) from funext fun x=>by rw [ht,Finset.sum_apply],ht a,← nitP]; exact nit _ _ _ fun i _=>hp i i
abbrev Warp (a b x:E): Token:= Reads.pluck ⟨0,L.P x a,L.P x b-L.P a a/2⟩
lemma warpR (δ:ℝ→ E)(a b x:E)(h:Reads δ ⟨0,a,b⟩):Reads (fun i=> Real.exp (L.P x (δ i)-L.P (δ i) (δ i)/2)) (Warp L a b x):=by
     apply Reads.expHop _ rfl; have hx:= Reads.smul (2:ℝ)⁻¹ (arb L _ h); convert (hush (L.P x) h).minus hx using 1; · funext i; dsimp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul];ring
     apply JetS.eta
     · change 0=0 + -(2⁻¹*0);ring
     · change _=_+ -(2⁻¹*0);ring
     change _=_+ -(2⁻¹* _);ring
omit [FiniteDimensional ℝ E] in
lemma warpB (a b:E):ScriptJ.B (Warp L a b):=by
     let f:E→ℝ:=fun i=>L.P i a; let g:E→ℝ:=fun i=>L.P i b-L.P a a/2; have hx:Bond f:=by rw [show f=L.P a from funext fun i=> L.turns ..]; exact Bond.glyph _
     have hv:Bond g:=by rw [show g= ⇑(L.P b) - fun i:E=>L.P a a/2 from funext fun i=>congr_arg (fun u:ℝ=>u-L.P a a/2) (L.turns i b)]; exact (Bond.glyph _).sub (Bond.keep _)
     apply Xbond (Bond.keep 1) hx; change Bond (fun i=> g i+(f i)^2/2); rw [show (fun i=>_)=g+(2:ℝ)⁻¹ • (f^2) from funext fun i=>by simp only [Pi.pow_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul];ring]; exact hv.add ((hx.pow 2).scale _)
end Stranded
end YM.OPE.Libra
