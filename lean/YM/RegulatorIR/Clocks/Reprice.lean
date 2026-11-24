import YM.RegulatorIR.Profiles.Chance
import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Re-express t in a single formal parameter

Mass-1 noise and denominator cancellation paid by reading theorem under
analytic continuation. Algebraic truncated ∀ coefficients. Inverses just
series; relevance to coupling probes requires detector theorem. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Clocks
open Function Budget Spatial Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Ledger.Sky Step Matrix StopB Ward Uniform Finset Halo Halo.Sight Gain Profiles Centered
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius Matrix
variable {p r n:ℕ}
abbrev Writing:= PowerSeries ℝ
variable {f g h θ τ:ℝ→ℝ}{x y s t:Writing}

lemma permits (h:coeff 0 s=0): PowerSeries.HasSubst s:= PowerSeries.HasSubst.of_constantCoeff_zero (show PowerSeries.constantCoeff s=0 from by rwa [coeff_zero_eq_constantCoeff_apply] at h)
-- `quote` method computes $(Σ t_i s^i)_j; explicitly through p
lemma quotes (U X:Writing)(h:coeff 0 X=0)(hp:r≤p): coeff r (U.subst X)=coeff r (∑ i∈Finset.range (p+1),PowerSeries.C (coeff i U)*X^i):=by
 have he n:= Squares.expo_near X 1 (fun i hi=> by rw [show i=0 from by omega,h]) (n:=n) (i:=r); rw [PowerSeries.coeff_subst' (permits h),map_sum]; simp_rw [PowerSeries.coeff_C_mul]
 apply finsum_eq_sum_of_support_subset
 intro i hi; by_contra! hv; apply hi;dsimp only;rw [show coeff r (X^i)=0 from he i (by simp only [Finset.mem_coe,Finset.mem_range] at hv;omega)]; exact mul_zero _
lemma substT (H:Squares p x y)(h:coeff 0 s=0)(hr:Squares p s t) : Squares p (x.subst s) (y.subst t):=by
 have ht: coeff 0 t=0:= h ▸ (hr 0 (Nat.zero_le _)).symm
 have hp i:Squares p (s^i) (t^i):= by induction i with
                                           | zero=>simp;exact fun _ _=>rfl
                                           | succ i ih=>rw [pow_succ,pow_succ]; exact ih.maintains hr
 intro i hi; rw [quotes x s h hi,quotes y t ht hi,map_sum,map_sum]; apply sum_congr rfl; intro j hj
 rw [coeff_C_mul,coeff_C_mul, hp j i hi, H j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]
lemma rateTry {S:Writing}(h: coeff 0 S=0)(hp: coeff 1 S≠0):∃ P:Writing, coeff 0 P=0∧coeff 1 P≠0∧ S.subst P=PowerSeries.X ∧ P.subst S=PowerSeries.X :=by
 have hv:IsUnit (S.coeff 1):= hp.isUnit; have he:PowerSeries.constantCoeff S=0:=by rwa [coeff_zero_eq_constantCoeff_apply] at h
 refine ⟨S.substInvOfIsUnit hv,?_,?_, S.subst_substInvOfIsUnit_right he hv,S.subst_substInvOfIsUnit_left he hv⟩
 · rw [coeff_zero_eq_constantCoeff_apply]; exact S.constantCoeff_substInvOfIsUnit hv
 rw [S.coeff_one_substInvOfIsUnit hv]; simp [hp]
lemma composed (h:coeff 0 x=0)(he:coeff 0 s=0)(T:Writing): PowerSeries.subst x (T.subst s : Writing)=T.subst (s.subst x):= subst_comp_subst_apply (permits he) (permits h) _
-- S expands coefficients in τ parameter; `$g=g(τ)` once x right, beyond mesh h.
structure Reset where
  bill : Writing
  invertU : Writing
  signal : coeff 0 bill=0
  allowed : coeff 1 bill≠0
  ready : coeff 0 invertU=0
  capable : coeff 1 invertU≠0
  strongI : bill.subst invertU=PowerSeries.X
  strongP : invertU.subst bill=PowerSeries.X
namespace Reset
variable (R:Reset)
def fromR (S: Writing)(h:coeff 0 S=0)(hp:coeff 1 S≠0): Reset:= ⟨S,(rateTry h hp).choose,h,hp,(rateTry h hp).choose_spec.1,(rateTry h hp).choose_spec.2.1,(rateTry h hp).choose_spec.2.2.1,(rateTry h hp).choose_spec.2.2.2⟩
lemma irrevocable (S: Writing): PowerSeries.subst R.invertU (S.subst R.bill)=S:=by rw [composed R.ready R.signal,R.strongI,PowerSeries.X_subst]
lemma introduces (S:Writing): PowerSeries.subst R.bill (S.subst R.invertU)=S:= by rw [composed R.signal R.ready,R.strongP,PowerSeries.X_subst]
end Reset

namespace Outlook
open Prim Tested
lemma script_pow (h: Script x f)(n:ℕ): Script (x^n) (f^n):=by induction n with
 | zero=>rw [pow_zero,pow_zero];exact (map_one _ : PowerSeries.C (R:=ℝ) 1=1) ▸ Script.oneC 1
 | succ n ih=>rw [pow_succ,pow_succ]; exact ih.mul h
lemma template (S:Writing)(P:Writing)(h: Script P g)(p:ℕ): Script (∑ i∈Finset.range (p+1), PowerSeries.C (coeff i S)*P^i) (peval (Tested.term S) p∘ g):=by
 let τ(i:ℕ):=(fun _:ℝ=>coeff i S)*g^i; let t(i:ℕ):= PowerSeries.C (coeff i S)*P^i; have hv:= Aspiration.sum (Finset.range (p+1)) τ (fun i=>Tested.term (t i)) (fun i _=> (Script.oneC _).mul (script_pow h i))
 unfold Script; convert hv using 1
 · ext1 y; simp only [peval,Zone.eval,Function.comp_apply,Finset.sum_apply]; apply sum_congr rfl; intro w _; rw [show τ w y= _ from rfl]; unfold τ; simp only [Pi.mul_apply,Pi.pow_apply]; exact mul_comm ..
 ext1 i; unfold Tested.term; rw [map_sum,Finset.sum_apply]
lemma pathTax {f : ℝ→ℝ}(h: Tested.Bill p f)(hp:Tested.Bill 1 g)(he: Tendsto g Tested.germ Tested.germ): Tested.Bill p (f∘g):=by
 obtain ⟨c,hc,h⟩:=h; obtain ⟨k,hk,H⟩:=hp; refine ⟨c*k^p,by positivity,?_⟩
 filter_upwards [Tested.eventually_pos, he.eventually Tested.eventually_pos,he.eventually h,H] with y hy hP hf hv
 change 0<g y at hP; rw [Real.norm_of_nonneg hP.le,pow_one] at hv
 apply le_trans hf; calc
   _ ≤ c*(k*y)^p:= by gcongr
   _ = _:= by rw [mul_pow,mul_assoc]
lemma tilted (H:Script x f)(B:Script y g)(h:coeff 0 y=0)(hp: Tendsto g Tested.germ Tested.germ) : Script (x.subst y) (f ∘ g):=by
 have hv: Tested.Bill 1 g:= by convert B 0 using 1; ext1 a; simp [peval, Zone.eval,Tested.term,h]
 intro k
 let T:=peval (Tested.term x) k;let F:=fun i:ℕ=> coeff i (x.subst y)
 have hQ := template x y B k
 let s:=∑ i∈Finset.range (k+1), PowerSeries.C (coeff i x)*y^i
 have hm:peval F k=peval (Tested.term s) k:= by ext1 p; apply sum_congr rfl;intro i hi; exact congr_arg (p^i*·) (quotes x y h (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
 have he : (f-T)∘ g+(T∘g-peval (Tested.term s) k)= f∘g-peval F k:= by rw [hm]; ext1 x;simp
 change Tested.Bill _ (f∘g-peval F k);rw [← he];exact Tested.bill_add (pathTax (H k) hv hp) (hQ k)
-- truncated power identity: from global Γ through p and Pose on aperture.
lemma arcs (h : ContDiffAt ℝ ∞ f 0)(he: f 0 ≠ 0):tale f⁻¹= (tale f)⁻¹:=by
 have hp:= (Script.actual h).inverse (show Tested.term _ 0≠0 from by rw [Tested.term,tale_base]; exact he); have ht :Tested.reciprocal (Tested.term (tale f))= Tested.term ((tale f)⁻¹):=by unfold Tested.reciprocal; rw [show PowerSeries.mk (Tested.term (tale f))= tale f from PowerSeries.ext (fun i=>coeff_mk ..)]
 rw [ht] at hp; exact Script.dictates (h.inv he) hp
end Outlook
end YM.RegulatorIR.Clocks
