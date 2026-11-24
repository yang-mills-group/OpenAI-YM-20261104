import YM.AllOrder.Ink.Echo
import YM.AllOrder.Ker.Transfer
import YM.Next.FREE_KERNELS.Traffic
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Ink
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace.SigmaP Ker
open Progress.ClassicalKin Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response
open scoped BigOperators Topology Classical ContDiff
variable {n m:Side} {α β : Type} [Fintype α] [Fintype β] {k N M:ℕ} {a C D b:ℝ}
namespace Rail
open GaussianScore
section price
variable {ι : Type} [Fintype ι] {f: Positions ι→ℝ} (H: Prices k C f)
def pullC : ℕ→ℕ→ℝ
  | 0, _ => 1
  | n+1, k => honor k * pullC n (k-1)
lemma pullC_pos (n k:ℕ):0<pullC n k:= by induction n generalizing k with | zero=> exact zero_lt_one | succ n ih=> exact mul_pos (honor_pos _) (ih _)
def mantle (j k:ℕ):=∑ i∈Finset.range (j+1),pullC i k
lemma can_pull (i k j:ℕ)(hi:i≤j): pullC i k≤mantle j k:=Finset.single_le_sum (f:=fun i=>pullC i k) (fun _i _=> (pullC_pos _ _).le) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
include H in
lemma ornament (v:Fin N→ι): ‖entry f 0 v‖≤ C*pullC N k:= by
 induction N generalizing k C f with
 | zero=> unfold pullC entry; simp only [iteratedFDeriv_zero_apply, mul_one]; simpa only [norm_zero,add_zero,one_pow,mul_one] using! H.2.2 0
 | succ y ih=>
    let j:= v (Fin.last y); let u:= diff' (bolt j) f; let Z(i:Fin y):=v i.castSucc; let L:= ContinuousLinearMap.apply ℝ ℝ (bolt j); have hv:= ih (H.taper (bolt j) (norm_bolt j).le) Z; rw [← show entry u 0 Z= entry f 0 v from ?_]; swap; · unfold entry; rw [show u=L ∘ fderiv ℝ f from rfl]; rw [L.iteratedFDeriv_comp_left (H.2.1.read.smooth.contDiffAt.fderiv_right (m:=ω) (by simp)) le_top, iteratedFDeriv_succ_apply_right]; rfl -- rw issue
    exact hv.trans_eq (mul_assoc ..) -- trans_eq notation?
lemma codeL (i:Fin k→ι)(j:ℕ): LinTest (Positions ι) j (fun f=>entry f 0 i):= ⟨fun _f _g h H=>congr_arg (fun A: ContinuousMultilinearMap ℝ (fun _ : Fin k=>Positions ι) ℝ=> A (fun a=> bolt (i a))) (iteratedFDeriv_add_apply (h.read.smooth.contDiffAt.of_le le_top) (H.read.smooth.contDiffAt.of_le le_top)),fun _f g h=> congr_arg (fun A:ContinuousMultilinearMap ℝ (fun _ : Fin k=>Positions ι) ℝ=> A (fun a=> bolt (i a))) (iteratedFDeriv_const_smul_apply (a:=g) (h.read.smooth.contDiffAt.of_le le_top))⟩
end price

omit [Fintype α] in
lemma le_window (z:Site n)(k:Point α) : separation z (stood z k).1 ≤ size k.1:= by
 rw [separation_comm,separation,stood]; change pdist ((z+_)-_)≤_; rw [add_comm z, add_sub_cancel_right]; exact Next.Free.within_size ..
omit [Fintype α] in
lemma asks (z:Site n)(S:Slip (Point α)): Requests Set.univ (invoice z S) Prod.fst z (meter S):= by
 intro v _ w _ h; induction S with
 | nil=>rfl
 | cons x S ih=>
   change v (stood z x) *invoice z S v=w (stood z x)*invoice z S w; rw [h (stood z x)];
   · exact congr_arg (w (stood z x)*·) (ih (fun i hi=>h i (by change separation _ _ ≤ size x.1 + meter S; omega)))
   apply (le_window ..).trans; exact Nat.le_add_right ..

def widthG (a:ℝ)(k:ℕ):= a/(k+1:ℕ)
lemma widthG_pos (ha:0<a):0<widthG a k:= div_pos ha (by positivity)
lemma horizon (z:Site n)(P:Slip (Point α))(k:ℕ)(h:P.length≤k)(v: Fin M→ Leaf n α)(he: M≤N)(ha:0<a) : ‖entry (invoice z P) 0 v‖ ≤ (mantle N k*Real.exp (a*meter P)) * Real.exp (-widthG a N * spanSites Prod.fst z v):= by
 let G:=widthG a N; let f:= invoice z P; let c:= mantle N k; have hc:0 ≤ c:= (pullC_pos 0 k).le.trans (can_pull 0 _ _ (Nat.zero_le N)); by_cases hH:∃ i:Fin M,meter P<separation z (v i).1; · obtain ⟨i,hi⟩:=hH; rw [(asks z P).zero univ_mem ((Field.ticket z P).2.1.read.smooth.contDiffAt.of_le le_top) v i hi.not_ge, norm_zero]; change 0≤ c *_ *_; positivity
 push Not at hH; have hv := (ornament (Prices.up h (Field.ticket z P)) v); rw [one_mul] at hv; refine (hv.trans (can_pull _ _ _ he)).trans ?_; let m:= spanSites Prod.fst z v; rw [mul_assoc, ← Real.exp_add]; apply le_mul_of_one_le_right hc (Real.one_le_exp ?_)
 have hP : m ≤ (N+1)*meter P:= (Finset.sum_le_sum (g:=fun _=>meter P) (fun i _=> hH i)).trans (by simpa using Nat.mul_le_mul_right (meter P) (show M ≤ N+1 from by omega))
 have hy:0<G:=widthG_pos ha; have he : G*m ≤ a*meter P:= calc
  _ ≤ G*((N+1:ℕ)*(meter P:ℝ)) := by apply mul_le_mul_of_nonneg_left ?_ hy.le; exact_mod_cast hP
  _ = _ := by unfold G widthG; field_simp
 change 0≤a*↑(meter P)+ -G*(m:ℝ); linarith
end Rail
end YM.AllOrder.Ink
