import Mathlib.Analysis.Calculus.Taylor
import YM.MSbar.TreeOPE.Script

/-!
# Taylor translation at degree zero in coupling

One radial shape at a time, exterior positions generic from contraction
point. Implements the free Taylor expansion on curvature jets, also
ensuring propagating solely through physical slot labels (no external leg
hypotheses). Output terms carry the FULL powers of normal-coordinate radius
(costed for the rescaled OPE at output weight). Truncation here per leg;
use grade projection later. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.OPE
open Function Set Filter Asymptotics Analysis
open Maxwell Maxwell.Free Maxwell.Wick
open Finsupp Next.Rank.Normal
open scoped ContDiff Topology BigOperators Classical
variable {G : Gauge} {k l j m : ℕ} {x y z : E4}

def translated (x : E4) (p : Probe G k) : (j : ℕ) → Probe G (k+j)
  | 0=>p
  | j+1=> raiseLeg x (translated x p j)

def stanza (j : ℕ) (x : E4) (r : ℂ) (p : Probe G k) := (r^(k+2+j)/(j.factorial:ℂ)) •
     reify (translated x p j)

def series (m : ℕ) (x : E4) (r : ℂ) (p : Slot G) := ∑ j∈Finset.range (m+1),stanza j x r (coordinateLeg p)
lemma stanza_txt (p : Probe G k) (j : ℕ) (r : ℂ) : glyph (stanza j x r p)=(r^(k+2+j)/(j.factorial:ℂ)) • symbol (k+j) (translated x p j) := by unfold stanza; rw [map_smul,reified]
lemma stanza_pure (p : Probe G k) (j : ℕ) (r : ℂ) : pureW scaleW (k+2+j) (glyph (stanza j x r p)):= by
  rw [stanza_txt,← MvPolynomial.C_mul',show k+2+j=k+j+2 from by omega]; exact (symbol_hom (translated x p j) (fun a=>a+2)).C_mul _
lemma stanza_resc (p : Probe G k) (j : ℕ) (r : ℂ) : glyph (stanza j x r p) = scale scaleW r (glyph (stanza j x 1 p)):= by
  rw [scaled_pure scaleW _ (k+2+j) _ (stanza_pure ..),stanza_txt,stanza_txt,smul_smul]; simp [div_eq_mul_inv]

lemma progress_add (m : ℕ) {x : E4} (p : Slot G) : through scaleW m (glyph (series m x 1 p)) (glyph (series (m+1) x 1 p)):= by
  intro j hj; unfold series tier; rw [Finset.sum_range_succ _ (m+1), map_add, map_add, (stanza_pure (coordinateLeg p) (m+1) (x:=x) (r:=1)).weightedHomogeneousComponent_ne (w:=scaleW) j (by omega)]
  simp

private lemma lineSmooth (p : Probe G k) (q : Probe G l) (r : ℝ) (h : z+r • x≠y) : ContDiffAt ℝ ∞ (fun t : ℝ=> (↑(K p q (z+t • x) y):ℂ)) r:= Complex.ofRealCLM.contDiff.contDiffAt.comp r ((K_smooth p q (z+r • x,y) h).comp r (f:=fun t:ℝ=>(z+t • x,y)) (by fun_prop))
private lemma derivatives (p : Probe G k) (q : Probe G l) (r : ℝ) (h : z+r • x≠y) (j : ℕ):
    iteratedDeriv j (fun t : ℝ=> (↑(K p q (z+t • x) y):ℂ)) r=↑(K (translated x p j) q (z+r • x) y):= by
  induction j generalizing r with
  | zero=> simp [translated]
  | succ j ih=>
    let L (t : ℝ) := z+t • x; let B(s:E4) := K (translated x p j) q s y; let T:= translated x p j
    have ht : DifferentiableAt ℝ B (L r):= (((K_smooth T q (L r,y) h).comp _ (f:=fun s:E4=>(s,y)) (by fun_prop)).differentiableAt (by simp))
    have he : HasDerivAt L x r:= by unfold L; simpa using ((hasDerivAt_id' r).smul_const x).const_add z
    rw [iteratedDeriv_succ]; refine (EventuallyEq.deriv_eq (f:=fun s:ℝ=>(↑(B (L s)):ℂ)) ?_).trans ?_
    · filter_upwards [(show Continuous L by unfold L; fun_prop).continuousAt.eventually (isOpen_ne.mem_nhds (show L r∈ {v | v≠y} from h))] with t H using ih t H
    have hA:= Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt r (ht.hasFDerivAt.comp_hasDerivAt r he)
    have hb : fderiv ℝ B (L r) x=K (raiseLeg x T) q (L r) y:= K_left_D _ _ h x
    exact hA.deriv.trans (congr_arg ((↑):ℝ→ℂ) hb)

private lemma prices (f : ℝ→ℂ) (m : ℕ) (hf : ContDiffAt ℝ ∞ f 0) :
    (fun r : ℝ=> f r-∑ i∈Finset.range (m+1), ((r^i)/(i.factorial:ℝ)) • iteratedDeriv i f 0)=O[𝓝 0] (fun r=>r^(m+1)) := by
  have hh := hf.of_le (show (↑(m+1:ℕ): WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  obtain ⟨u,hu,h⟩:= Metric.mem_nhds_iff.mp (hh.eventually (by simp)); let S:= Metric.ball (0:ℝ) u; have hs : 0∈S:= Metric.mem_ball_self hu
  have ht := taylor_isLittleO (f:=f) (n:=m+1) (convex_ball (0:ℝ) u) hs (fun x hx=> ((show ContDiffAt ℝ (↑(m+1:ℕ)) f x from h hx)).contDiffWithinAt)
  have he : 𝓝[S] 0=𝓝 0:=  nhdsWithin_eq_nhds.mpr (Metric.isOpen_ball.mem_nhds hs)
  rw [he] at ht; let p:=fun (r:ℝ) (i:ℕ)=>((r^i)/(i.factorial:ℝ)) • iteratedDeriv i f 0
  have ha (r : ℝ): taylorWithinEval f (m+1) S 0 r= ∑ i∈Finset.range (m+1+1),p r i:= by rw [taylor_within_apply]; apply Finset.sum_congr rfl; intro i _; rw [iteratedDerivWithin_of_isOpen (s:=S) Metric.isOpen_ball hs]; simp [p, div_eq_inv_mul]
  let D := iteratedDeriv (m+1) f 0; let C : ℂ := ((↑(m+1).factorial:ℂ))⁻¹*D
  have H(r:ℝ): p r (m+1)=C * (r:ℂ)^(m+1):= by unfold p C D; rw [Complex.real_smul, div_eq_inv_mul, Complex.ofReal_mul]; push_cast; ring
  have H' : (fun r:ℝ=>C*(r:ℂ)^(m+1)) =O[𝓝 0] (fun r:ℝ=>r^(m+1)):= IsBigO.const_mul_left (isBigO_of_le _ (fun r=> le_of_eq (by rw [norm_pow, norm_pow,Complex.norm_real]))) _
  have he(r:ℝ) : f r-∑ i∈Finset.range (m+1),p r i=f r-(∑ i∈Finset.range (m+1+1),p r i)+C*(r:ℂ)^(m+1):= by rw [Finset.sum_range_succ _ (m+1), H]; ring
  change (fun r=> f r-∑ i∈Finset.range (m+1),p r i)=O[_] _; simp_rw [he]; apply IsBigO.add _ H';
  unfold S at ha; simp_rw [sub_zero,ha] at ht; exact ht.isBigO

lemma leg_close (p q : Slot G) (m : ℕ) (x : E4) (h : z≠y) :
    Accords (𝓝 0) (fun r:ℝ=>r^(m+1)) (fun r:ℝ=>(r:ℂ)^(scaleW p)*entry p q (z+r • x) y) (fun r:ℝ=> linearCombination ℂ (fun w=>entry w q z y) (series m x r p)):= by
  let E (r:ℝ):= entry p q (z+r • x) y
  have hp : ContDiffAt ℝ ∞ E 0:=lineSmooth (x:=x) (z:=z) (coordinateLeg p) _ 0 (by simp [h])
  let A (r:ℝ):=(r:ℂ)^(scaleW p); have hA : Continuous A:= by unfold A; fun_prop
  let R (r:ℝ) (i:ℕ) := (r^i/(i.factorial:ℝ)) • iteratedDeriv i E 0
  have hh (r:ℝ) : linearCombination ℂ (fun w=>entry w q z y) (series m x r p) = A r * ∑ i∈Finset.range (m+1),R r i:= by
    unfold series; rw [map_sum,Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _
    have hv : iteratedDeriv i E 0=↑(K (translated x (coordinateLeg p) i) (coordinateLeg q) z y):= by simpa only [zero_smul,add_zero,E, K, entry] using derivatives (coordinateLeg p) (coordinateLeg q) (x:=x) (z:=z) 0 (by simpa) i
    unfold R stanza; rw [map_smul,show linearCombination ℂ (fun w=>entry w q z y) _ = _ from at_leg (translated x (coordinateLeg p) i) (coordinateLeg q) z y h, hv]; simp only [A,scaleW, smul_eq_mul,Complex.real_smul]; push_cast; ring
  simp_rw [hh]; apply Accords.close _ _ ((show ContinuousAt (fun r:ℝ=> r^(m+1)) 0 from (by fun_prop)).tendsto.isBigO_one ℝ)
  · change (fun r:ℝ=> A r*_ - A r*_)=O[_] _; simp_rw [← mul_sub]; simpa only [one_mul] using (hA.continuousAt (x:=0) |>.tendsto.isBigO_one ℝ).mul (prices E m hp)
  exact ((show ContinuousAt (fun r:ℝ=> A r* ∑ i∈Finset.range (m+1), R r i) 0 from ((by unfold R; fun_prop))).tendsto).isBigO_one ℝ
end YM.MSbar.OPE

namespace YM.MSbar.OPE
open Function Set Filter Asymptotics Analysis
open Maxwell Maxwell.Free Maxwell.Wick
open Finsupp Next.Rank.Normal
open scoped ContDiff Topology BigOperators Classical
variable {G : Gauge} {k l j m : ℕ} (r : ℂ) (x : E4)

-- expose series expression via `rewired`, so H/color equivariance easy
lemma many (i : Slot G) : glyph (series m x r i)=∑ j∈Finset.range (m+1),(r^(i.1+2+j)/(j.factorial:ℂ)) • ((rewired (glide G x))^[j] (MvPolynomial.X i)) := by
  unfold series; rw [map_sum]
  have ht (j): ((rewired (glide G x))^[j] (MvPolynomial.X i))=symbol (i.1+j) (translated x (coordinateLeg i) j):= by
    induction j with
    | zero=> simp [translated,symbol_coordinate]
    | succ j h=> rw [iterate_succ_apply',h,rewired_symbol]; rfl
  apply Finset.sum_congr rfl; intro j _; rw [ht,stanza_txt]
private def traveled (m k : ℕ) : poly (Slot G) →ₗ[ℂ] poly (Slot G) :=
    ∑ j∈Finset.range (m+1),(r^(k+2+j)/(j.factorial:ℂ)) • (((rewired (glide G x)).toLinearMap) ^ j)
private lemma traveled_apply (m : ℕ) (i : Slot G): traveled r x m i.1 (MvPolynomial.X i) = glyph (series m x r i):= by
  rw [many,traveled, LinearMap.sum_apply]; apply Finset.sum_congr rfl; intro j _; rw [LinearMap.smul_apply, Module.End.pow_apply]; rfl
lemma rotate_transport (g : G.El) : (pigment g).comp (Next.Rank.Normal.exchange (series (G:=G) m x r))=(Next.Rank.Normal.exchange (series m x r)).comp (pigment g):= by
  let T:=traveled (G:=G) r x m; let E:=Next.Rank.Normal.exchange (series (G:=G) m x r); let D:=rewired (glide G x)
  have he(p:WickPol G) : D (pigment g p)=pigment g (D p):= by
    refine morph_wire (glide G x) (glide G x) (pigment g).toRingHom (fun i p=>p.comp (castFace g i)) (fun t=> ⟨t,MvPolynomial.algHom_C ..⟩) (fun _ v=>symbol_pigment g v) (fun j v=>?_) _; ext1 A; exact congr_arg v (color_lower _ _ _).symm
  have ht (j:ℕ) (p:WickPol G): (D.toLinearMap^j) (pigment g p)=pigment g ((D.toLinearMap^j) p):= by
    simp_rw [Module.End.pow_apply]; induction j with
    | zero=> rfl
    | succ j h => rw [iterate_succ_apply',iterate_succ_apply',h]; exact he _
  ext1 i; rw [AlgHom.comp_apply,AlgHom.comp_apply, exchange_x,← traveled_apply]
  have H (y : Probe G i.1): T i.1 (symbol i.1 y)=E (symbol i.1 y):= by
    unfold symbol; simp_rw [← show ∀ (t:ℂ) (p:WickPol G), t • p=MvPolynomial.C t*p from fun t p=>(MvPolynomial.C_mul' ..).symm, map_sum,map_smul]; apply Finset.sum_congr rfl; intro j _; congr! 1; exact (traveled_apply r x m (⟨i.1,j⟩:Slot G)).trans (exchange_x ..).symm
  rw [show Next.Rank.Normal.exchange _ (pigment g (MvPolynomial.X i))=traveled r x m i.1 (pigment g (MvPolynomial.X i)) from (by rw [pigment, MvPolynomial.aeval_X]; exact (H _).symm)]
  unfold traveled; rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]; apply Finset.sum_congr rfl; intro j _; rw [LinearMap.smul_apply,LinearMap.smul_apply,map_smul, show (rewired (glide G x)).toLinearMap^j=D.toLinearMap^j from rfl,ht]
end YM.MSbar.OPE
