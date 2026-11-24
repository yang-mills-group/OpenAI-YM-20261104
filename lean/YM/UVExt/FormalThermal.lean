import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Scalar exponential interpolation on V-jet rules. Does not assert joint analytic estimates by analyticity alone (pays separate real budgets at staggered trial values). -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExt.EnergyRay.Thermal
open Filter Set Finset ContinuousLinearMap FormalMultilinearSeries
open scoped Topology ContDiff BigOperators

variable {E F B : Type*} [NormedAddCommGroup E][NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup B] [NormedSpace ℝ B]
variable {f g : E → F} {p q : F → B} {n : ℕ} {x : E}
structure JetEq (n : ℕ) (x : E) (f g : E→F) : Prop where
  L : ContDiffAt ℝ (n:ℕ∞ω) f x
  R : ContDiffAt ℝ (n:ℕ∞ω) g x
  agree (j : ℕ) : j≤n → iteratedFDeriv ℝ j f x=iteratedFDeriv ℝ j g x
namespace JetEq
lemma main (h : JetEq n x f g) : f x=g x := DFunLike.congr_fun (β:=fun _=>_) (h.agree 0 (Nat.zero_le n)) 0
lemma refl (hf : ContDiffAt ℝ n f x) : JetEq n x f f := ⟨hf,hf,fun _ _=>rfl⟩
lemma trans {g'} (h : JetEq n x f g) (h' : JetEq n x g g') : JetEq n x f g' := ⟨h.L,h'.R,fun i hi => (h.agree i hi).trans (h'.agree i hi)⟩
theorem chain (h : JetEq n x f g) (h' : JetEq n (f x) p q) : JetEq n x (p ∘ f) (q ∘ g) := by
    refine ⟨h'.L.comp _ h.L, (h.main ▸ h'.R : ContDiffAt ℝ ↑n q (g x)).comp _ h.R, ?_⟩
    intro j hj
    have hi : ↑j ≤ (↑n:ℕ∞ω) := Nat.cast_le.mpr hj
    rw [iteratedFDeriv_comp h'.L h.L hi,iteratedFDeriv_comp (h.main ▸ h'.R) h.R hi,← h.main]
    unfold FormalMultilinearSeries.taylorComp ftaylorSeries
    apply Finset.sum_congr rfl; intro c _
    dsimp [FormalMultilinearSeries.compAlongOrderedFinpartition]; rw [h'.agree _ (c.length_le.trans hj)]
    congr 1 with i; rw [h.agree (c.partSize i) ((c.partSize_le i).trans hj)]
lemma multiply (f : E → ℂ) {g h : E→ℂ} (hf : ContDiffAt ℝ n f x) (hg : JetEq n x g h) : JetEq n x (fun i=> f i*g i) (fun i=> f i*h i) := by
  apply JetEq.chain (f:=fun i=> (f i,g i)) (g:=fun i=> (f i,h i)) (p:=fun q: ℂ × ℂ  => q.1 * q.2) (q:=fun q=>q.1*q.2)
  · refine ⟨hf.prodMk hg.L,hf.prodMk hg.R,fun i hi=> ?_⟩
    rw [iteratedFDeriv_prodMk hf hg.L, iteratedFDeriv_prodMk hf hg.R,hg.agree i hi]
    all_goals exact_mod_cast hi
  exact JetEq.refl (contDiffAt_fst.mul contDiffAt_snd)
lemma line {f g : ℝ→B} {x : ℝ} (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x) (h : ∀ i,i ≤ n → iteratedDeriv i f x = iteratedDeriv i g x) : JetEq n x f g :=
  ⟨hf, hg, fun i hi=> (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin i) B).symm.injective (h i hi)⟩
end JetEq

variable {ι : Type*} [Fintype ι]

def heat (b y : ℂ) (s:ℝ) := Complex.exp (b*((s:ℂ)-y))
lemma heat_action (b y : ℂ) (s:ℝ) (k:ℕ) : iteratedDeriv k (heat b y) s = b^k*heat b y s := by
  induction k generalizing s with
  | zero => simp
  | succ k ih =>
     have hx : HasDerivAt (fun s:ℝ => b*((s:ℂ)-y)) b s := by
         simpa [sub_eq_add_neg] using ((Complex.ofRealCLM.hasFDerivAt (x:=s)|>.hasDerivAt.sub_const y).const_mul b)
     have hp := ((hx.cexp).const_mul (b^k)).deriv
     rw [iteratedDeriv_succ,funext ih]; change deriv _ s = _; unfold heat; rw [show deriv _ s = _ from hp,pow_succ]; ring
lemma heat_jets (n : ℕ) (u : ℂ) (r L : ι→ℂ) (s : ℝ) (h : ∀ k ≤ n, u^k = ∑ i:ι,L i*(r i)^k) : JetEq n s (heat u s) (fun t=>∑ i:ι,L i * heat (r i) s t) := by
  have hf (n : ℕ) (r : ℂ) (C : ℂ) : ContDiffAt ℝ (n:ℕ∞ω) (fun t=>C * heat r s t) s := by
     change ContDiffAt ℝ ↑n (fun t=>C * Complex.exp (r*(Complex.ofRealCLM t-_))) _
     fun_prop
  apply JetEq.line (by simpa [one_mul] using hf n u 1) (show ContDiffAt ℝ ↑n _ s from ContDiffAt.sum (s:=Finset.univ) (fun i _ => hf n (r i) (L i)))
  intro i hi; rw [@iteratedDeriv_eq_iteratedFDeriv _ _ _ _ _ i (fun t=>∑ b,L b*heat (r b) s t), iteratedFDeriv_fun_sum_apply (fun b _=>hf i (r b) (L b)), _root_.sum_apply]
  have hz a : iteratedDeriv i (fun t=>L a*heat (r a) s t) s=L a*(r a)^i := by rw [iteratedDeriv_const_mul _ (show ContDiffAt ℝ ↑i (fun t=>heat (r a) s t) s by simpa using hf i (r a) 1),heat_action]; simp [heat]
  simp_rw [← iteratedDeriv_eq_iteratedFDeriv, hz, heat_action]; simpa [heat] using h i hi

lemma thermal_jet {b A : E → ℂ} {f : ℂ→E→ℂ} (x : E) (hf : ∀ z t, f z t = A t*Complex.exp (z*(b t))) (n : ℕ) (hb : ContDiffAt ℝ n b x) (hreal : ∀ t, t∈Set.range Complex.ofReal → ContDiffAt ℝ n (f t) x) (hbR : ∀ i,(b i).im=0)
    (u : ℂ) (r L : ι→ℂ) (h : ∀ k ≤ n,u^k=∑ i,L i*(r i)^k) : JetEq n x (f u) (fun t=>∑ i,L i* Complex.exp ((u-r i)*b x)*f (r i) t) := by
  have hA := show ContDiffAt ℝ n A x from by simpa [show f 0 = A from funext fun i=> by simp [hf]] using hreal 0 ⟨0,rfl⟩
  let b' t:= (b t).re; have he: JetEq n x b' b' := JetEq.refl (Complex.reCLM.contDiff.contDiffAt.comp x hb)
  have hh := JetEq.multiply (fun t=>A t*Complex.exp (u*b x)) (hA.mul contDiffAt_const) (he.chain (heat_jets n u r L (b' x) h))
  simp only [Function.comp_apply,b'] at hh
  have hz i : ((b i).re:ℂ)=b i:= (Complex.ext rfl (hbR i).symm)
  simp_rw [heat, hz] at hh
  simp_rw [mul_sum] at hh
  convert! hh using 1 <;> ext t
  · rw [hf, mul_sub, Complex.exp_sub]; field_simp [Complex.exp_ne_zero]
  apply sum_congr rfl; intro i _
  rw [hf,show r i*(b t-b x)=_ from mul_sub _ _ _, sub_mul,Complex.exp_sub,Complex.exp_sub]; ring
end YM.UVExt.EnergyRay.Thermal

namespace YM.UVExt.EnergyRay.Thermal
open Filter Set Finset ContinuousLinearMap
open scoped Topology ContDiff BigOperators
variable {E : Type*}[NormedAddCommGroup E][NormedSpace ℝ E] {x : E}
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {j n : ℕ}
private def spline (r : ι→ℂ) (x : ℂ) (i : ι) := (Lagrange.basis Finset.univ r i).eval x
lemma sample (r : ι → ℝ) (h : Function.Injective r) (hj : j ≤ n) (hn : n < Fintype.card ι) (x : ℂ) :
    x^j = ∑ i:ι,spline (fun i=> r i) x i*(r i)^j := by
 let r' i:=(r i:ℂ); have hh:= Lagrange.eq_interpolate (f:=(Polynomial.X:Polynomial ℂ)^j) ((show Function.Injective r' from Complex.ofReal_injective.comp h).injOn (s:=(↑(Finset.univ : Finset ι) : Set ι)))
 have hp : (Polynomial.X:Polynomial ℂ)^j=_ := hh (by rw [Polynomial.degree_X_pow]; exact_mod_cast hj.trans_lt hn)
 apply_fun Polynomial.eval x at hp
 rw [Polynomial.eval_pow, Polynomial.eval_X,Lagrange.interpolate_apply,Polynomial.eval_finsetSum] at hp
 exact hp.trans (sum_congr rfl fun i _=> by rw [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,mul_comm]; rfl)
lemma bound_spline {r : ι → ℝ} {z:ℂ} {δ C:ℝ} (hδ : 0<δ) (hi : ∀ i i':ι, i≠i' → δ ≤ ‖r i-r i'‖) (hn: Fintype.card ι = n+1) (hh : ∀ i, ‖z-(r i:ℂ)‖ ≤ C*δ) (i : ι) : ‖spline (fun i=>r i) z i‖ ≤ C^n := by
 have hC : 0≤C := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hh i)) hδ
 rw [spline,Lagrange.basis,Polynomial.eval_prod,norm_prod]
 calc
   _ ≤ ∏ j∈ univ.erase i,C := prod_le_prod (fun _ _=> norm_nonneg _) (fun j hj=> ?_)
   _ = _ := by rw [prod_const,card_erase_of_mem (mem_univ i),card_univ,hn,Nat.add_sub_cancel_right]
 simp only [Lagrange.basisDivisor, Polynomial.eval_C,Polynomial.eval_mul,Polynomial.eval_sub,Polynomial.eval_X,norm_mul,norm_inv,← Complex.ofReal_sub, Complex.norm_real]
 apply (inv_mul_le_iff₀ ?_).2 ?_
 · exact hδ.trans_le (hi i j ((mem_erase.mp hj).1.symm))
 rw [mul_comm _ C]; exact (hh j).trans (mul_le_mul_of_nonneg_left (hi i j (mem_erase.mp hj).1.symm) hC)

private lemma norm_smul (f : E → ℂ) (C : ℂ) {x : E} (hp : ContDiffAt ℝ n f x) : ‖iteratedFDeriv ℝ n (fun t=>C*f t) x‖ = ‖C‖ * ‖iteratedFDeriv ℝ n f x‖ := by
 rw [show (fun t=>C*f t) = ((C:ℂ) • f) from rfl, iteratedFDeriv_const_smul_apply hp]
 rw [_root_.norm_smul]

/-- One-sided interpolation of an exponential vertex. No continuity assumption on coefficients of other variables than the displayed real-field argument. The angular price uses real derivatives through n only at one nearby one-sided mesh. For the formal heat arguments the heat-independent remaining term must be regular (e.g. hold frozen inputs), and a rank count for a polynomial density normalization is kept. The hidden prefactor per vertex in the leading bound can be chosen independent of n. -/
lemma thermal_response {b A : E → ℝ} {f : ℂ→E→ℂ} (x : E) (hf : ∀ (z:ℂ) t, f z t = (A t:ℂ)*Complex.exp (z*(b t))) (n : ℕ) (hb : ContDiffAt ℝ n b x) {d : ℕ}
    {u : ℂ} (r : ι→ℝ) {m:ℕ} (hn : Fintype.card ι=m+1) (hnn : n≤m) {δ C D : ℝ}
    (hδ : 0<δ) (hSe : ∀ i j, i≠j → δ ≤ ‖r i-r j‖) (hMesh : ∀ i,‖u-(r i:ℂ)‖ ≤ C*δ)
    (hscale : 0≤D) (hs : ∀ i, ‖u‖ ≤ D^2*(r i)) (hX : ∀ i,0 < r i)
    (hside : ∀ i, (u.re-r i)*b x ≤ 0)
    (hjet : ∀ i, ContDiffAt ℝ n (fun t=> (Real.sqrt (r i)^d:ℂ)*f (r i) t) x)
    {k : ℂ} (hk : ‖k‖ = Real.sqrt ‖u‖ ^ d) :
    ContDiffAt ℝ n (f u) x ∧ ‖iteratedFDeriv ℝ n (fun t=> k*f u t) x‖ ≤ D^d*C^m*(∑ i,‖iteratedFDeriv ℝ n (fun t=> (Real.sqrt (r i)^d:ℂ)*f (r i) t) x‖) := by
 haveI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
 let start:= Classical.arbitrary ι
 have hpos i : (0:ℝ)<(Real.sqrt (r i):ℝ)^d := by positivity [hX i]
 have hr : Function.Injective r := by intro i j h; by_contra! hn; have hSe := hSe i j hn; simp [h] at hSe; linarith
 have hb' := Complex.ofRealCLM.contDiff.contDiffAt.comp x hb
 have hA : ContDiffAt ℝ n (fun i=>(A i:ℂ)) x := by
   let s:ℂ := Real.sqrt (r start)^d
   have hs0 : s ≠ 0 := by change (Real.sqrt (r start):ℂ)^d ≠_; exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hX start)).ne')
   let ex t:=Complex.exp (-(r start:ℂ)*b t); have he : ContDiffAt ℝ n ex x := Complex.contDiff_exp.contDiffAt.comp _ (contDiffAt_const.mul hb')
   have h : ContDiffAt ℝ ↑n (fun t=> s⁻¹*ex t*((s*f (r start) t))) x:= (contDiffAt_const.mul he).mul (hjet start)
   apply ContDiffAt.congr_of_eventuallyEq h
   apply Filter.Eventually.of_forall; intro t
   change _ = _ * (_*f _ t); rw [hf]; unfold ex; rw [neg_mul, Complex.exp_neg]; field_simp [hs0, Complex.exp_ne_zero]
 have hv (z) : ContDiffAt ℝ n (f z) x := by
     rw [funext (hf z)]; exact hA.mul (Complex.contDiff_exp.contDiffAt.comp _ (contDiffAt_const.mul hb'))
 refine ⟨hv u,?_⟩
 let p i := spline (fun i=> (r i:ℂ)) u i * Complex.exp ((u-(r i:ℂ))*b x)
 have hp := (thermal_jet (E:=E) (b:=Complex.ofReal ∘ b) (A:=Complex.ofReal ∘ A) (f:=f) x hf n hb' (fun t _=> hv _) (fun _=> rfl) u _ _ (fun j h=> by simpa using sample r hr h (by omega : n< Fintype.card ι) u)).agree n le_rfl
 change iteratedFDeriv ℝ n (f u) x=iteratedFDeriv ℝ n (fun t=>∑ i, p i*f (r i) t) x at hp
 rw [norm_smul _ _ (hv u),hk,hp,iteratedFDeriv_fun_sum_apply (fun i _=>contDiffAt_const.mul (hv _))]
 apply le_trans (mul_le_mul_of_nonneg_left (norm_sum_le ..) (by positivity)); rw [mul_sum,mul_sum]; apply sum_le_sum
 intro i _; rw [norm_smul _ _ (hv _), norm_smul _ _ (hv _)]
 have hV := Real.sqrt_le_sqrt (hs i); rw [Real.sqrt_mul (sq_nonneg _) _, Real.sqrt_sq hscale] at hV
 have hU : ‖p i‖ ≤ C^m := by
    unfold p; rw [norm_mul,Complex.norm_exp]; have ht:=hside i; have he := bound_spline hδ hSe hn hMesh i
    simp only [Complex.mul_re,Complex.ofReal_im,mul_zero,sub_zero,Complex.ofReal_re,Complex.sub_re] -- might collapse
    exact ((mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.mpr ht))).trans he
 have hK : ‖(Real.sqrt (r i):ℂ)^d‖=Real.sqrt (r i)^d := by rw [_root_.norm_pow, Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _)]
 rw [hK]; have hx := pow_le_pow_left₀ (Real.sqrt_nonneg ‖u‖) hV d; rw [mul_pow] at hx
 apply le_trans (mul_le_mul hx (mul_le_mul_of_nonneg_right hU (norm_nonneg _)) (by positivity) ?_)
 · ring_nf; exact le_rfl
 · positivity
end YM.UVExt.EnergyRay.Thermal
