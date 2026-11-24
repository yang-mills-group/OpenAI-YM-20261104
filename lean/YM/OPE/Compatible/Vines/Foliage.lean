import YM.OPE.Compatible.Channel.Near
import YM.Next.FREE_KERNELS.Traffic
/-! # WideScript - x-space cover multilinear evaluation. real arbitrary palettes -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free
open scoped Topology BigOperators Classical
variable {r d m:ℕ}{c:ℝ}{I T W:Type*}{f:Filter I}{V:I→ Side}
namespace Script
open Page
abbrev fieldX (T:Type*):= Cover × T→ℝ
abbrev Quiet (u:fieldX T)(d:ℕ):Prop:=∃ C:ℝ,0≤C ∧ ∀ i, ‖u i‖ ≤ C*poise d i.1
abbrev Glob (u:Fin r → fieldX T)(d:Fin r→ℕ):Prop:=∀ i,Quiet (u i) (d i)
def wordX (u: Fin r→ fieldX T)(i: Page T r):=∏ j,u j (i j)
def wholeX (p:Script T r)(u: Fin r →fieldX T):= ∑' i,p i*wordX u i
variable {u v:Fin r→fieldX T}{k:Fin r→ℕ}{p:Script T r}
lemma wordXbill {b:Fin r→ℝ} (hz:0≤b) (h:∀ i x,‖u i x‖≤b i * poise (k i) x.1) (hg:∑ i,k i≤m) (x:Page T r):‖wordX u x‖≤(∏ i,b i)*figure m x:=by
   rw [wordX,norm_prod]; let v:ℝ:= stamp x; have he:1≤v:=by unfold v; exact_mod_cast (notch_one x.xy)
   have ht(i:Fin r):‖u i (x i)‖ ≤ b i* v^(k i):=by
      have hx : notch (x i).1 ≤ stamp x:=by unfold notch; rw [perimeter]; exact Nat.add_le_add_left (single_le_sum (f:=fun i:Fin r=>size (x i).1) (fun _ _=>Nat.zero_le _) (mem_univ i)) _
      exact (h i _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) (by unfold v; exact_mod_cast hx) _) (hz i))
   apply (prod_le_prod (fun _ _=> norm_nonneg _) (fun i _=>ht i)).trans; rw [prod_mul_distrib,Finset.prod_pow_eq_pow_sum]; exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ he hg) (prod_nonneg fun i _=>hz i)
lemma wordSum (h:soot m p c) (hu:Glob u k) (hk:∑ i,k i ≤ m): Summable fun i=>p i*wordX u i:=by
   choose b hb hh using hu; let z:= ∏ i,b i; let w (i: Page T r):ℝ:=figure m i*‖p i‖; refine (show Summable w from h.2.1).mul_left z|>.of_norm_bounded (fun i=>?_)
   rw [norm_mul]; apply (mul_le_mul_of_nonneg_left (wordXbill hb hh hk i) (norm_nonneg _)).trans; unfold z w; exact le_of_eq (by ring)
abbrev unfoldX {n:Side} (x:deck T n):fieldX T:= fun p=>x (wrap n p.1,p.2)
abbrev closeX (x:fieldX T)(n:Side):deck T n:=fun p=> x (lift p.1,p.2)
lemma bridgeX {n:Side}(u: Fin r→deck T n)(p:Script T r): scribe 0 p u=wholeX p fun i=>unfoldX (u i):=by unfold scribe wholeX; simp [render,wordX]
structure Realized (V:I→ Side) (f: Filter I)(u:fieldX T)(x:∀ i:I, deck T (V i))(d:ℕ):Prop where
  Once :∃ b:ℝ,0≤b ∧ ∀ i a,‖unfoldX (x i) a‖ ≤ b*poise d a.1
  Onset (j:Cover×T) : Tendsto (fun i=> unfoldX (x i) j) f (𝓝 (u j))
lemma received (hv:Tendsto (fun i=>(V i).val) f atTop){u:fieldX T}(h:Quiet u d):Realized V f u (fun i=>closeX u (V i)) d:=by
    constructor
    · obtain ⟨c,hc,g⟩:= h; refine ⟨c,hc,fun i a=>?_⟩; apply (g (lift (wrap (V i) a.1),a.2)).trans; apply mul_le_mul_of_nonneg_left _ hc; simp only [poise,notch]; gcongr; exact sum_le_sum fun j _=>below_wrap ..
    intro j; apply tendsto_const_nhds.congr'; filter_upwards [eventually_unfold V hv j.1] with i hi; change u j=u _; rw [hi]
lemma keepX (h:soot m p c) (x:∀ j:I,Fin r→ deck T (V j))(hr:∀ i, Realized V f (u i) (fun j=> x j i) (k i))(hk:∑ i,k i≤m): Tendsto (fun j=> scribe (0:Site (V j)) p (x j)) f (𝓝 (wholeX p u)):=by
    choose b hb hh using fun i=>(hr i).Once; let z:= ∏ i,b i; let g (i:I)(a:Fin r):fieldX T:=unfoldX (x i a); simp_rw [bridgeX]; change Tendsto (fun i=> wholeX p (g i)) _ _; unfold wholeX
    let w(i:Page T r):= figure m i*‖p i‖; refine tendsto_tsum_of_dominated_convergence ((show Summable w from h.2.1).mul_left z) (fun i=> Tendsto.const_mul _ (tendsto_finsetProd _ fun t _=> (hr t).Onset _)) (Eventually.of_forall fun i q=>?_)
    rw [norm_mul]; apply (mul_le_mul_of_nonneg_left (wordXbill hb (u:=g i) (fun a y=> hh a i y) hk q) (norm_nonneg _)).trans; unfold z w; exact le_of_eq (by ring)
end Script
end YM.OPE.Flume
