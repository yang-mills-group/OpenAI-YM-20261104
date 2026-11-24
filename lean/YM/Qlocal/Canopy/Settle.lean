import YM.Qlocal.Canopy.Lithe
/-!
 # Keeping clock-independent gauges at true derivatives of the connected log
 Without assuming bounds on invoice shape & test continuation. Products mixing full momentum
 before meeting truncations. No loss of actual radius in output (*two^j* implicit payroll from v).
 No radius requirement except nonnegative from Cover.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Canopy
open Function Finset Filter Topology
open AllOrder Ker Laplace Laplace.SigmaP Response Catch Catch.Clock PositionX.Jet
open ConnectedActivityE6 Blaze Brush PertExtension PertExtension.Series
open PhysicalNext Repeat Fare Lapis
open scoped Topology ContDiff BigOperators Classical
variable {ι σ : Type*} {S: Catch.Clock ι}{X:ι→ Type} [∀ i,NormedAddCommGroup (X i)] [∀ i,NormedSpace ℝ (X i)][∀ i,FiniteDimensional ℝ (X i)]
    {j k q n m r:ℕ} {d t:ι→ℝ}{a b g:∀ i,X i→ℝ}{A B :ℝ}{x:∀ i,X i}
namespace Lithe
variable (A0 B0 : Tape X)
def fuse (A B:Tape X): Tape X:=fun i x=> Laplace.SigmaP.plus (A i x) (B i x)
-- use constant ℝ versions.Polly.
lemma settle (A B:Word ℝ)(v:ℝ)(q:ℕ): PositionX.Jet.delay (plus A B) q v= ∑ i∈range (q+1), (v^i * A i) * PositionX.Jet.delay B (q-i) v:= by
 let C : ℕ→ ℝ→ℝ:= fun i _=> B i; have he := delay_right (ι:=Unit) (i:=()) (V:=fun _=>ℝ) (f:=C) (t:=v) (n:=q) (c:=A); let f:= fun u:ℝ→ℝ=> u 0
 have hp j: forming A C j (0:ℝ)= plus A B j:= by unfold forming; rw [Finset.sum_apply,plus_sum,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]; rfl
 have hh n : PositionX.Jet.delay C n v 0=PositionX.Jet.delay B n v:= by unfold PositionX.Jet.delay; rw [Finset.sum_apply]; rfl
 replace he:= congr_arg f he; unfold f at he; rw [Finset.sum_apply] at he
 simp_rw [Pi.smul_apply,smul_eq_mul, hh] at he -- both? LHS.Eager labels
 rw [← he]; unfold PositionX.Jet.delay; rw [Finset.sum_apply]; simp_rw [Pi.smul_apply,hp] -- left.A.
namespace Sail
variable (ht:S.Meter t (-(1/2))) (hd:∀ᶠ i in S.rail,0 ≤ d i)
variable {P Q:Tape X} (hp:Sail S t d j k P a x)(hq:Sail S t d j k Q b x)
local notation "Hx"=>Catch.Cover S j
include ht hd hp hq
lemma united : Sail S t d j k (fuse P Q) (a*b) x:= by
 refine ⟨fun i hi=>?_,(daylight hp.total hq.total).weak (by simp),fun n hn=>?_⟩
 · let f (p:ℕ) (i':ι):= (fun (x:X i')=> P i' x p * Q i' x (i-p)); have hh : Hx 0 d (fun i' => ∑ p ∈ range (i+1),f p i') x:= Catch.Cover.booking (range (i+1)) (fun p he=> (daylight (hp.wage _ (by have hv:= mem_range.mp he; omega)) (hq.wage _ (by omega))).weak (by simp)) hd
   refine hh.home (Eventually.of_forall fun j=>?_); ext1 u; unfold fuse; rw [Finset.sum_apply,plus_sum,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
 let g(p:ℕ)i':X i'→ℝ:= fun u=> (t i')^p * P i' u p; let v (p:ℕ)i:= g p i*(b i-beam Q (n-p) t i); let D(i):= fun x:X i=> (a*b) i x-beam (fuse P Q) n t i x; let h i:= a i-beam P n t i
 have hv : D=fun i=> h i*b i+∑ p∈range (n+1),v p i:= by
    ext i u; unfold D v fuse; rw [Pi.add_apply,Finset.sum_apply]; simp_rw [Pi.mul_apply,Pi.sub_apply]; unfold g h beam; rw [settle,Pi.sub_apply]
    simp only [mul_sub,sum_sub_distrib,sub_mul,PositionX.Jet.delay, smul_eq_mul,Finset.sum_mul]; ring
 have hw p (hv:p∈range (n+1)): Catch.Cover S j (graded (n+1)) d (v p) x:= by -- binder `v` shadow, `d` shadow actual.Edit
    have he:= mem_range.mp hv; have hh: p+(n-p)+1=n+1:=by omega
    have hu:Catch.Cover S j (graded p) d (g p) x:= ((hp.wage p (by omega)).caliber (ht.pow p)).weak (by unfold graded; simp) -- caller `g` scale scalar.S.
    exact (daylight hu (hq.cost (n-p) (by omega))).weak (by unfold graded; have h : (p:ℝ)+(↑(n-p):ℝ)+(1:ℕ)=(n+1:ℕ):=(by exact_mod_cast hh); push_cast at *; nlinarith only [h]) -- edit
 change Hx (graded (n+1)) d D x; rw [hv]; exact (((daylight (hp.cost n hn) hq.total)|>.weak (by simp)).add (Catch.Cover.booking _ hw hd))
end Sail
end Lithe
end YM.Qlocal.Canopy
