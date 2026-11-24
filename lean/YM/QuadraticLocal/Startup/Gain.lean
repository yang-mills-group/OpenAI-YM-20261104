import YM.Integration.LocalComparisonPackets
import YM.QuadraticLocal.Germ.Focal
/-!
# High-grade analytic local marked launch test inputs and currency on the represented path

Finite lists of fixed-rank integral, arbitrary lengths/powers subject to stated bounds, orientation
already from cover paths and on actual curvature completions at real fields. Integrated top-down
IF larger than comparison scale per mode. Preserve origins, source root, length and stamp rank,
coin for each path & ALL slots of test-linear. This vocabulary doesn't stipulate its periodization
from canonical formal path, but uses Token interface. ℤ lag powers of g. These are eligible also
for partial comparison at HIGH RANK/prefix and its restoration with K in q step; don't cover all mark types.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Spes
open Function Filter Finset Lattice Wilson RG Marker MeasureTheory Push Push.AbsoluteSums Animals
open Affinity Display Integration.LocalComparison ComparisonDensity.Address Comparison.Density.RenderM
open AnalyticBridge.VerifiedReset AnalyticBridge.VerifiedReset.Collection Precision Exterior Extra.Iteration Next.Scheduling Next.Foundations
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {V I:Type}[DecidableEq V]{R:Census V}{G:Gauge}{n:Side} {k r d s :ℕ}
variable {D: V → Orbit}(P:BudgetPoint)
set_option quotPrecheck false
local notation "C"=> (fun v =>(D v).Mood)
local notation "T'"=> TestSpace D -- use Full
local notation "T"=> Affinity.Full (E:=C)
local notation "X"=> Display.Lens.portion D
local notation "Fam"=> Token G n C
variable (K:∀v,Submodule ℂ (D v).Mood)(L:V→Support n){m:R.Mode}{o:V→Site n}
local notation "z"=> Lens.portion D
section Token
structure Legal (K:∀v,Submodule ℂ (D v).Mood) (L:V→Support n) (m:R.Mode) (F:Token G n C k):Prop where
    positive : 0 ≤ F.coin
    credit : ∀ t: Affinity.Wallet (Lens.portion D), (∑ i, ‖F.gem i (Affinity.readBack z t)‖) ≤ F.coin
    frame v : v ∈ m.val → L v ⊆ F.plot
    wears : ∀ t:T, (F.re t).length ≤ F.fall ∧ (F.re t).footprint F.root ⊆ F.plot
    legend (t:T)(U)(g:G.El): F.touch t (fun i=> G.adjoint g (U i))=F.touch t U
    gems j : Affinity.Eligible K m.val (F.gem j)

namespace Legal
variable (F:Token G n (fun v=>(D v).Mood) k) -- note `C` notation issue var!
variable (hL: Legal K L m F)
include hL
lemma traced (t:T): (F.re t).Invariant∧(F.im t).Invariant:=by refine ⟨fun g U=>?_,fun g U=>?_⟩; rw [← (F.real_and_imag ..).1,hL.legend,(F.real_and_imag ..).1]; rw [← (F.real_and_imag ..).2,hL.legend,(F.real_and_imag ..).2]
lemma sizing (t: Wallet (Lens.portion D)) (u':T)(he:u'=Affinity.readBack z t): (F.re u').magnitude ≤ F.coin ∧ (F.im u').magnitude ≤ F.coin:= by subst u'; exact ⟨le_trans (Finset.sum_le_sum (fun i _=> Complex.abs_re_le_norm (F.gem i _))) (hL.credit t), le_trans (Finset.sum_le_sum (fun i _=> Complex.abs_im_le_norm (F.gem i _))) (hL.credit t)⟩
lemma honor (t:T): P.Regular F.plot (F.read t):= by
   rw [F.reading]; refine regular_larger (regular_add (regular_mapped Complex.ofRealCLM ?_) (regular_smul _ (regular_mapped Complex.ofRealCLM ?_))) (hL.wears t).2
   · exact Derivs.canonical_regular _ _ P (traced _ _ _ hL t).1
   exact Derivs.canonical_regular _ _ P (traced _ _ _ hL t).2
lemma reads (U:Config G n): Eligible K m.val fun t=> F.read t U:=by
   let b (i:Chroma (G:=G) k) :ℂ:=↑(∏ j,(F.path j).atSite U F.root (i j)); -- fix invocation
   have h0(k): Eligible K m.val fun t=> b k * F.gem k t:= (hL.gems k).cs (b k)
   refine ⟨RG3.Held.Letter.total univ (fun i t=> b i * F.gem i t) (fun i _=>(h0 i).full),fun i hi t ht=>?_⟩; exact sum_eq_zero fun j _=> (h0 j).hollow i hi t ht
omit hL in
lemma charge (F: Token G n C k)(t:T) : Continuous (F.read t):=by rw [F.reading]; exact (Complex.continuous_ofReal.comp ((F.re t).unmasked_cont _)).add ((Complex.continuous_ofReal.comp ((F.im t).unmasked_cont _)).const_smul Complex.I)
omit hL in
lemma beyond (F:Token G n C k)(t:T)(U:Config G n) {c:ℝ} (hs:(F.re t).magnitude ≤ c)(ht:(F.im t).magnitude ≤ c) : ‖F.read t U‖≤2*c*(2:ℝ)^k:=by
   rw [F.reading]; simp only [Pi.add_apply,Pi.smul_apply]; refine (norm_add_le ..).trans ?_
   rw [norm_smul,Complex.norm_real,Complex.norm_real,Complex.norm_I,one_mul,show 2*c*2^k=c*2^k+c*2^k from (by ring)]; exact add_le_add (((F.re t).unmasked_bound ..).trans (mul_le_mul_of_nonneg_right hs (by positivity))) (((F.im t).unmasked_bound ..).trans (mul_le_mul_of_nonneg_right ht (by positivity)))
open Wages
-- `pays_can` numeric bound from Slope.Customer.A.P CL unable call because Normed instances only imported, unused warnings but cannot use on unit.Char. 
def baseCost (P:BudgetPoint)(G:Gauge)(k d r:ℕ) : ℝ:= ((1+r:ℝ)^P.power)^P.order * (2* startup G k P.power P.order * P.threshold^k*(1+d:ℝ)^grade k P.power P.order)
lemma mantle (t:Wallet (Lens.portion D))(t':T)(he:t'=Affinity.readBack z t)(hD:F.fall ≤ d)(hM:F.plot⊆ neighbors r F.root) (x:Site n)(hx:x∈F.plot): P.supBounds x F.plot (F.read t') (baseCost P G k d r * F.coin):=by
   let a:=startup G k P.power P.order; let C':= F.coin; let f:= a*P.threshold^k* (1+(d:ℝ))^(grade k P.power P.order) * C'
   obtain ⟨hL',hL''⟩:= sizing _ _ _ hL t t' he
   have hv(V:Atom G k)(hp:V.length≤ d)(hm:V.magnitude ≤ F.coin): price P V ≤ f:=by
       unfold f a; rw [Wages.scan]; have hV:= (0:ℝ); have ha:0≤ Wages.startup G k P.power P.order:= by unfold Wages.startup; have ht:=lt_of_lt_of_le zero_lt_one (slot_ge G P.power P.order 0); positivity
       have hz:=P.threshold_pos; calc _ ≤ a*P.threshold^k*F.coin *((d:ℝ)+1)^grade k P.power P.order:= by unfold a; have hx : 0≤ V.magnitude:=(by unfold Atom.magnitude; positivity); have hz0:= hL.positive; gcongr
                                       _ = _:= by unfold a C'; ring
   obtain ⟨hv₁,hv₂⟩:= traced K L F hL t'; have ht:= Derivs.canonical_regular (F.re t') F.root P hv₁; have hx':= Derivs.canonical_regular (F.im t') F.root P hv₂; have hp: (F.re t').length≤d:=le_trans (hL.wears t'|>.1) hD
   have hR:P.supBounds F.root F.plot (F.read t') (2*f):= by
       rw [two_mul,F.reading]; let h1:=(sup_real ht).2 (Wages.total P (F.re t') F.root); let h2:=bound_smul Complex.I ((sup_real hx').2 (Wages.total P (F.im t') F.root)); rw [Complex.norm_I,one_mul] at h2; exact bound_larger (bound_add (regular_mapped Complex.ofRealCLM ht) (regular_smul _ (regular_mapped Complex.ofRealCLM hx')) (Local.bound_weaken h1 (hv _ hp hL')) (Local.bound_weaken h2 (hv _ hp hL''))) (hL.wears _).2
   let a':=(1+(r:ℝ))^P.power; refine Local.bound_weaken (Local.bound_shift hR (honor P K L F hL t') _) (le_trans ?_ (?_: a'^ P.order *(2*f) ≤ _)); rotate_left; · exact le_of_eq (by unfold baseCost f a a' C'; ring)
   apply mul_le_mul_of_nonneg_right _ hR.1; unfold a'; gcongr; exact ((neighbors_mem ..).mp (hM hx)) -- orientation?
open Comparison.RG02 Comparison.RG02.Assembly
-- grade for germs with actual test address independent and slot ordering. Valid even without hL. Requires Leg support & symbol.Conv η orientation afterwards.
omit hL in
private lemma eternal (a : Atom G k)(x:Site n): ContDiffAt ℝ ω (fun v:Directions G n => a.unmasked (increment 1 v) x) 0:= by
  -- proof from `canonical_regular`
  have hi : ContDiffAt ℝ ω (fun v => Work.F02.atomExt a x (Work.F02.physical (increment 1 v))) 0 := (Work.F02.atomExt_contDiff a x).restrict_scalars ℝ |>.contDiffAt.comp 0 (Work.F02.physical_contDiffAt (A:=increment 1) (fun i => by simp only [increment,G.mat_mul]; exact ((G.exp_jet.comp (contDiff_apply ..)).mul contDiff_const).contDiffAt))
  convert Complex.reCLM.contDiff.contDiffAt.comp _ hi using 1
  ext1; simp only [Function.comp_apply, Work.F02.atomExt_physical,Complex.reCLM_apply, Complex.ofReal_re]
omit hL in
lemma factual (F:Token G n C k)(t:T) : Comparison.RG02.Assembly.GradeAt k (Comparison.RG02.Bulk.projected (fun _=> F.read t)) := by
   let l : GradeAt k (F.read t ∘ increment 1):=⟨?_,fun i hi=> Token.order_z F t hi⟩
   · let c x:= collect G (n:=n) x; let V(x:ℝ×fieldDir G n 1):Directions G n:=c x.2; exact GradeAt.coarse (g:=V) l ((by apply ContDiff.contDiffAt; unfold V c Exterior.collect; fun_prop) : ContDiffAt ℝ ω V 0) rfl; -- order goals shift
   rw [F.reading]; exact (Complex.ofRealCLM.contDiff.contDiffAt.comp (g:=Complex.ofRealCLM) _ (eternal ..)).add ((Complex.ofRealCLM.contDiff.contDiffAt.comp (g:=Complex.ofRealCLM) _ (eternal (F.im t) F.root)).const_smul Complex.I)
end Legal
end Token
end YM.QuadraticLocal.Spes
