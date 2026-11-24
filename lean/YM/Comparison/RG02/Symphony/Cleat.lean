import YM.Comparison.RG02.Adjacent.Attached
import YM.Comparison.RG02.Symmetry.Turn
/-!
# Extra transverse Ward check on torus kinetic prescription

Take Hessian in the `patrol` Ward identities in a way that respects motion of the
rescaled fields. No subtraction of previously matched jets needed here unlike general-arity
horizontal leading extraction. Use gauge paths dilated in radial/external units, use common
quadratic homogeneity and the *derived* vanishing on every affine term, then cross. On ANY
rank-priced analytic sheet. No complex momentum estimates or infinite-volume/source readout
assumed. Keeps all derivative orders.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Symphony
open Function Filter Finset MeasureTheory RG Precision Lattice Wilson Exterior Tree
open PertExtension.Series PertExtension.Series.Tested
open Marker Multi Order YM.Next.SectorChange Integral Laplace Symmetry Symmetry.Orbit
open Moving Moving.Path Moving.Shift Valence Adjacent Assembly
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {V:Type} [DecidableEq V] [Fintype V] {R:Census V}
    {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]
    {G:Gauge}{c:Side}{r k:ℕ}
local notation "X"=> fieldDir G c 1
namespace Cleat
abbrev scale (x:ℝ→E) (u:ℝ) (t:ℝ):=u • x (u*t)
private lemma stays (u:ℝ){x : ℝ→X} (hp:glows x): glows (scale x u):= by
    have he (t:ℝ) : ContDiff ℝ ω (fun x:ℝ=>t * x) := contDiff_const.mul contDiff_id
    exact ContDiffAt.const_smul (c:=u) (ContDiffAt.comp (f:=fun x:ℝ=> u*x) _ (show ContDiffAt ℝ ω x (u*0) from (mul_zero u).symm ▸ hp) (he u).contDiffAt)
private lemma within {u:ℝ}{x y:ℝ→X} (hu:0<u)(hp: Flow x y) : Flow (scale x u) (scale y u) := by
    let a(t:ℝ):=u*t
    have ha : Tendsto a along along:= tendsto_nhdsWithin_iff.mpr ⟨  (by simpa [a] using! (((continuous_const (y:=u)).mul continuous_id).continuousAt (x:=(0:ℝ))|>.mono_left (show along ≤ 𝓝 0 from nhdsWithin_le_nhds))), eventually_pos.mono fun t ht=>mul_pos hu ht⟩
    rcases hp with ⟨z,L,h,h'⟩; refine ⟨z,L ∘ a, h.comp ha, (ha.eventually h').mono fun t ht=>?_⟩
    have hv (x:ℝ→X) : sample t (scale x u t)=sample (a t) (x (a t)) := by unfold sample scale a; rw [smul_smul,mul_comm t u]
    rw [hv,hv]; exact ht

private lemma adapt {f:ℝ→ℂ} (u:ℝ) (he:ContDiffAt ℝ ω f 0) : motion (fun x=>f (u*x)) k=(u:ℂ)^k *motion f k := by
   let A:=u • ContinuousLinearMap.id ℝ ℝ; change motion (f ∘ A) _= _ ; unfold motion; rw [jet_continuous_right A (he.of_le le_top)]; change Assembly.jet f k ((u:ℝ)• 1)=_; rw [Clipper.weight,Complex.real_smul,Complex.ofReal_pow]
variable {m : ℕ→ℤ} {n i:ℕ} {p:Display (fieldDir G c 1)} {x y:ℝ→fieldDir G c 1}(h:Sheet r p)(hp:Charge r m p)(hx:glows x)
private def tally (p:Display X) (x:ℝ→fieldDir G c 1)(k i n:ℕ) (u:ℝ) := (u:ℂ)^(n+i) * motion (jet (p k) n ∘ x) i
omit h hp hx in
private lemma straight(k i n:ℕ): ContDiffAt ℝ ω (tally p x k i n) 0:= (Complex.ofRealCLM.contDiff.contDiffAt.pow _).mul contDiffAt_const
private def allBits(p:Display X) (x:ℝ→fieldDir G c 1)(m:ℕ→ℤ)(k i:ℕ)(u:ℝ):= ∑ n∈range (max (m k).toNat 2 + 1), tally p x k i n u
include h hp hx
private lemma count (he:k≤r)(i:ℕ)(u:ℝ) : motion (p k ∘ scale x u) i= allBits p x m k i u := by
   let T:=max (m k).toNat 2; have H : Level (T:ℤ) (p k) := (hp k he).promote (le_trans (Int.self_le_toNat _) (by exact_mod_cast (show _ from le_max_left (m k).toNat 2)))
   have hj (n:ℕ): ContDiff ℝ ω (jet (p k) n):= (levelJet ((h.known k he).contDiffAt) _).smooth
   unfold allBits; rw [show p k ∘ scale x u = _ from funext fun a=> H.posted (scale x u a), msum (L:=range (T+1)) _]

   · apply sum_congr rfl; intro n hn; unfold scale tally; simp_rw [Clipper.weight, Complex.real_smul, Complex.ofReal_pow]; let f:= jet (p k) n∘ x
     have ht : ContDiffAt ℝ ω f 0:= (hj n).contDiffAt.comp (0:ℝ) hx
     have ha : ContDiffAt ℝ ω (fun t:ℝ=> f (u*t)) 0:= by exact ContDiffAt.comp (g:=f) (f:=fun x:ℝ=> u*x) (0:ℝ) ((mul_zero u).symm ▸ ht) (contDiffAt_const.mul contDiffAt_id)
     change motion (fun a=> (u:ℂ)^n * f (u*a)) i= _ * motion f i; rw [mscale _ ha,adapt u ht, pow_add,mul_assoc]
   exact fun i _=> (hj i).contDiffAt.comp _ (stays u hx)

private def sumBits(p:Display X) (x:ℝ→fieldDir G c 1)(m:ℕ→ℤ)(k:ℕ)(u:ℝ):= ∑ i∈range (k+1),allBits p x m (k-i) i u
private lemma seeking (he:k≤r)(u:ℝ): sumBits p x m k u=patrol k p (scale x u):= (sum_congr rfl fun i _=> count h hp hx (le_trans (Nat.sub_le k i) he) i u).symm
omit h hp hx in
private lemma coming (k:ℕ) : ContDiffAt ℝ ω (sumBits p x m k) 0:= ContDiffAt.sum fun _ _=> ContDiffAt.sum fun _ _=> straight ..
omit hp hx in
private lemma sliced (he:k≤r)(hG:G.Simple)(hn:n+i=2)(hi:i≠0): tally p x k i n=0:= by
    have hv : n≤1:= by omega
    interval_cases n
    · unfold tally; simp_rw [Function.comp_def, jet_zero, mconst, if_neg hi, mul_zero]; rfl
    have hf:= h.color_grad he hG; unfold tally; simp_rw [Function.comp_def, Assembly.jet,iteratedFDeriv_one_apply,hf,_root_.zero_apply,smul_zero,mconst,if_neg hi,mul_zero]; rfl
omit hp hx
omit h in
private lemma located(k i n:ℕ): motion (tally p x k i n) 2= if n+i=2 then motion (jet (p k) n∘ x) i else 0:=by unfold tally; rw [mono_price contDiffAt_const, mconst]; split_ifs <;> first|rfl|omega
private lemma placed (he:k≤r) (hG:G.Simple)(i:ℕ) : motion (allBits p x m k i) 2= if i=0 then jet (p k) 2 (x 0) else 0 := by
    unfold allBits; rw [msum _ _ fun i _=>straight ..]; by_cases ht:i=0; subst i; simp_rw [located,Nat.add_zero, mzero]; rw [if_pos trivial, sum_ite_eq', if_pos (mem_range_succ_iff.mpr (le_max_right ..))]; rfl
    rw [if_neg ht]; refine sum_eq_zero fun n _=>?_ ; by_cases hv:n+i=2
    · rw [sliced h he hG hv ht]; apply (mconst _ _|>.trans ?_); simp
    rw [located k i n,if_neg hv]
private lemma isolated (he:k≤r)(hG:G.Simple): motion (sumBits p x m k) 2=jet (p k) 2 (x 0) := by
   unfold sumBits; rw [msum _ (fun i=> allBits p x m (k-i) i) fun i _=>ContDiffAt.sum fun j _=>straight ..]; simp_rw [show ∀ i:ℕ,motion (allBits p x m (k-i) i) 2 = _ from fun i=> placed h (le_trans (Nat.sub_le k i) he) hG i]; rw [sum_ite_eq',if_pos (by simp),Nat.sub_zero]
include hp hx
lemma forth(he:k≤r)(hG:G.Simple)(hy:glows y)(hf:Flow x y): jet (p k) 2 (x 0)=jet (p k) 2 (y 0):= by
   let f:=sumBits p x m k; let g:=sumBits p y m k
   have hh : f=ᶠ[along] g:= eventually_pos.mono fun i hi=> by rw [show f i=_ from seeking h hp hx he i, show g i=_ from seeking h hp hy he i]; exact h.follows _ _ (within hi hf) (stays i hx) (stays i hy) k he
   rw [← show motion f 2=_ from isolated h he hG, ← show motion g 2=_ from isolated h he hG]; exact trial_gap (trial_congr hh (Moving.Path.ordinary (f:=f) ((coming k).of_le le_top) 2)) (Moving.Path.ordinary (f:=g) ((coming k).of_le le_top) 2) 2 le_rfl
omit hx
open Matrix
lemma groove(he:k≤r)(hG:G.Simple)(u: fieldDir G c 0)(v: fieldDir G c 1) : iteratedFDeriv ℝ 2 (p k) 0 ![dColor G c 0 u,v]=0 := by
   let y:=dColor G c 0 u; let D:= fun a b:X => (iteratedFDeriv ℝ 2 (p k) 0) ![a,b]
   have hz(x:X): jet (p k) 2 (x+y)=jet (p k) 2 x := by unfold y; rw [← descends u x]; exact forth h hp (descent_smooth ..) he hG (hy:=contDiffAt_const) (hf:=ascendance ..)
   have hD(x:X):D (x+y) (x+y)=D x x:= by
       apply (smul_right_inj (show (Nat.factorial 2 : ℝ)⁻¹≠0 by positivity)).mp
       have he(x:X): D x x=iteratedFDeriv ℝ 2 (p k) 0 (fun _=>x) := by unfold D; congr 1; ext1 j; fin_cases j <;> rfl
       rw [he,he]; exact hz x
   let T:= fderiv ℝ (fderiv ℝ (p k)) 0
   have hp':D y y=0:= by simpa [D,iteratedFDeriv_two_apply] using hD 0
   have ht(x z:X): D x z=T x z:= iteratedFDeriv_two_apply ..
   have hm:T v y=T y v:= (h.known k he).contDiffAt.isSymmSndFDerivAt_of_omega ..
   have hh:= hD v; simp_rw [ht] at hh hp'; simp only [map_add,_root_.add_apply,hp',add_zero,hm] at hh; change D y v=_; rw [ht]; linear_combination hh/2
end Cleat
end YM.Comparison.RG02.Symphony
