import YM.MS.Wilson.Elect
import YangMills.WilsonProof.NativeSupport.YM.MS.Lifting.Brand
/-!
# Actual pure-basis jets for all orientations

Allow negative-swap plaquette, including zero. Dressed expressions are closed under
 based-lattice rule before scaling.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Native.Studio
open Function Filter Set Finset Plane Koszul Cylinder Lab Taylor Lattice Native Bare Focus Landau Draft Sew Chart Wilsonian
open Book Convolve Program Paint Color Logarithm Lifting Orient
open scoped Topology ContDiff
variable {G:Gauge} {F:Dot G Cover} {P Q:Type}[AddCommGroup P] [AddCommGroup Q] (d:Chart.Rail P)(L:Plaq)
-- orient pair. avoid nonempty issue on equality.
abbrev pos (x y:Axis)(h:x<y) : PlaqAxes:=⟨(x,y),h⟩
def ropeV (x:P) (c: CI G) : Dot G P:= if h: L.i < L.j then clot d (pos _ _ h) L.jets x c else if v:L.j < L.i then -clot d (pos _ _ v) L.jets x c else 0
def ropeF (x:P)(c:CI G) : Eye G P:= if h:L.i<L.j then α c ∘ edgeSense d (pos _ _ h) L.jets x else if z:L.j<L.i then -(α c ∘ edgeSense d (pos _ _ z) L.jets x) else 0
lemma rope_move (r:P→ Q)(g:Chart.Rail Q)(h:∀ i k,r (i+d k)=r i+g k)(x:P)(i:CI G): transport r (ropeV d L x i)=ropeV g L (r x) i:= by unfold ropeV; split_ifs ; exact clot_go d _ r g h _ _ _; rw [map_neg,clot_go d _ r g h]; exact map_zero _
lemma ropeT (x:P)(i:CI G): Tuned (ropeV d L x i) 0:= by
    unfold ropeV; split_ifs; apply clot_tuned; · rename_i h; simpa only [neg_one_smul ℂ (clot d (pos _ _ h) L.jets x i)] using (clot_tuned d (pos _ _ h) L.jets x i).cash (-1:ℂ) (by simp)
    exact Tune.zero
lemma ropeCheap (x:P)(i:CI G): From (ropeV d L x i).val 1:= by unfold ropeV; split_ifs; apply clot_low; rename_i h v; exact (fun i' h=> by rw [Submodule.coe_neg,Pi.neg_apply,clot_low d _ L.jets x i i' h,neg_zero]); exact fun _ _=>rfl
lemma rope_trans (x:P)(c:CI G) (g:P→ G.El)(U:Rig G P): ropeF d L x c (siteGauge d g U) = ∑ k: CI G,weight (g x)⁻¹ k c *ropeF d L x k U:= by
    unfold ropeF; split
    next h=> exact see ..
    next h => split
              next k=> simp_rw [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]; exact congr_arg Neg.neg (see ..)
              next k=> simp

def monV (d:Chart.Rail P)(x:P) : (k:ℕ)→ (Fin k→ Plaq)→ Grid G k → Dot G P
   | 0, _,_=> Cylinder.piece (1:ℂ)
   | n+1, f,c=> couple DotFlip (ropeV d (f 0) x (c 0)) (monV d x n (f ∘ Fin.succ) (c ∘ Fin.succ))
lemma mon_m (r:P→Q)(g:Chart.Rail Q)(h:∀ i k,r (i+d k)=r i+g k)(x:P)(n:ℕ)(f:Fin n→ Plaq)(u:Grid G n): transport r (monV d x n f u)=monV g (r x) n f u:= by induction n with | zero=> exact coin_settled _ _ | succ n ih=> rw [monV,monV,transport_comes,rope_move d _ r g h,ih]
lemma mon_T (x:P)(n:ℕ)(f:Fin n→ Plaq)(u:Grid G n): Tuned (monV d x n f u) 0:= by induction n with| zero=> exact ⟨coin_symm _,by intro i h; cases i; contradiction; rfl, fun i=> by rw [monV,piece]; cases i <;> simp [coin]⟩| succ n ih=> exact (ropeT d (f 0) x (u 0)).pair (ih ..)
lemma mon_L (x:P)(n:ℕ)(f:Fin n→ Plaq)(u:Grid G n): From (monV d x n f u).val n := by induction n with | zero=> exact fun _ _=> by omega | succ n ih=> push_cast; rw [add_comm (n:ℤ) 1]; exact (ropeCheap d (f 0) x (u 0)).pair (ih (f ∘ Fin.succ) (u ∘ Fin.succ))

def monF (n:ℕ) (x:P)(f:Fin n→ Plaq)(i: Grid G n)(U:Rig G P):ℝ:= ∏ j, ropeF d (f j) x (i j) U
lemma mon_trans (x:P)(n:ℕ)(f:Fin n→ Plaq)(u: Grid G n)(g:P→ G.El)(U:Rig G P): monF d n x f u (siteGauge d g U) = ∑ k:Grid G n, Lifting.ink (g x)⁻¹ k u * monF d n x f k U := by simp_rw [monF,rope_trans, Lifting.ink,Fintype.prod_sum, ← Finset.prod_mul_distrib]

section
variable [Fintype P][DecidableEq P]
lemma rope_R (x:P)(i:CI G): Reads (ropeV d L x i) (ropeF d L x i):= by
   unfold ropeV ropeF; split_ifs; exact clot_read ..; · rename_i v; simpa only [neg_one_smul ℂ (clot d (pos _ _ v) L.jets x i),neg_one_smul ℝ,Complex.ofReal_neg,Complex.ofReal_one] using (clot_read d (pos _ _ v) L.jets x i).cash (-1)
   refine ⟨contDiffAt_const,?_⟩; change 0= Cylinder.Taylor.ink _ 0; rw [ink_zero]
lemma mon_R (x:P)(n:ℕ)(f:Fin n→ Plaq)(u: Grid G n): Reads (monV d x n f u) (monF d n x f u):= by
    induction n with
    | zero=>
       rw [show monF d 0 x f u=fun _:Rig G P=> (1:ℝ) from funext fun U=>by simp [monF]]
       refine ⟨contDiffAt_const,?_⟩; change coin (1:ℂ)=Cylinder.Taylor.ink _ (fun _=>1); simp only [ink_const,Complex.ofReal_one]
    | succ n ih=> rw [show monF d (n+1) x f u= ropeF d (f 0) x (u 0)*monF d n x (f ∘ Fin.succ) (u ∘ Fin.succ) from funext fun U=> by simp only [monF, Pi.mul_apply,Fin.prod_univ_succ,Function.comp_apply]]; exact (rope_R d _ x (u 0)).pair (ih ..)
end

def realF (n:ℕ)(x:P)(f:Fin n→ Plaq)(i:Grid G n):= ∑ k:Grid G n,Lifting.group G k i • monF d n x f k
def realV (n:ℕ)(x:P)(f:Fin n→ Plaq)(i:Grid G n):= ∑ k:Grid G n,(Lifting.group G k i:ℂ) • monV d x n f k
lemma sings (n:ℕ)(x:P)(f:Fin n→ Plaq)(i:Grid G n): OpenGauge d (realF d n x f i):= by
    intro g U; simp_rw [realF,Finset.sum_apply,Pi.smul_apply, smul_eq_mul, mon_trans,Finset.mul_sum]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl (fun k _=>?_); simp_rw [← mul_assoc, mul_comm (Lifting.group G _ _), ← Finset.sum_mul,paysInk]; rw [mul_comm]
lemma sings_go (r:P→Q)(g:Chart.Rail Q)(h:∀ i k,r (i+d k)= r i+g k)(n:ℕ)(x:P)(f:Fin n→ Plaq)(u:Grid G n): transport r (realV d n x f u)= realV g n (r x) f u:= by simp_rw [realV,map_sum,map_smul,mon_m d r g h]
lemma real_t (n:ℕ)(x:P)(f:Fin n→ Plaq)(u: Grid G n): Tuned (realV d n x f u) 0:= Tune.sum _ fun j _=> (mon_T d x n f j).cash _ (by simp)
lemma real_F (n:ℕ)(x:P)(f:Fin n→ Plaq)(u:Grid G n): From (realV d n x f u).val n:= by rw [realV,sum_stack]; exact From.sum _ fun j _=> (mon_L d x _ _ j).smul _
lemma real_R [Fintype P][DecidableEq P](n:ℕ)(x:P)(f:Fin n→ Plaq)(u:Grid G n): Reads (realV d n x f u) (realF d n x f u):= Reads.sum _ fun j _=> (mon_R d x _ _ j).cash _
def markP (n:ℕ)(f:Fin n→ Plaq)(u:Grid G n):= realV idRail n (0:Cover) f u
lemma real_A (n:ℕ)(f:Fin n→ Plaq)(u:Grid G n): Aura (markP n f u) n:= by
   refine ⟨real_F idRail n 0 f u, real_t ..,fun k=>⟨realF (drive k) n 0 f u,sings (drive k) n 0 f u, (real_R ..).born,?_⟩⟩; change (transport _ (realV idRail _ _ _ _)).val=_; rw [sings_go (g:=drive k) _ _ (atlas k),map_zero]; exact (real_R ..).home
end YM.MS.Native.Studio
