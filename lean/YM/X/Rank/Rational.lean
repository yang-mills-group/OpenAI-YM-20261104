import YM.X.Rank.Canvas
import YM.Next.MAXWELL.House
/-!
Rationality of the leg-to-leg kernels of the target free limit. Off the
coincidence point **in Euclidean positions**. No density input.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PositionX.Rank
open Function Set Filter Maxwell Wick Maxwell.Free Tensor Analysis MvPolynomial
open scoped BigOperators Classical RealInnerProductSpace ContDiff Topology
variable {G : Gauge} {j l s : ℕ} {x : E4} {p : Gauge.Simple G}
namespace Rad
abbrev P := MvPolynomial Axis ℝ
abbrev here (x : E4) := (aeval (WithLp.ofLp x) : P →ₐ[ℝ] ℝ)
def dom : P := ∑ a : Axis, X a^2
@[simp] lemma dom_at (x : E4) : here x dom = ‖x‖^2 := by
  simp only [dom, here,map_sum,map_pow,aeval_X]
  rw [← real_inner_self_eq_norm_sq,inner4]; simp only [sq]

variable (u:E4)
private def slash := MvPolynomial.mkDerivation ℝ (fun i:Axis=>C (σ:=Axis) (u i))
private lemma derive (R : P) : DifferentiableAt ℝ (fun x=>here x R) x ∧ D u (fun x=>here x R) x = here x (slash u R) := by
  induction R using MvPolynomial.induction_on with
  | C c => simp only [here,aeval_C,Algebra.algebraMap_self,RingHom.id_apply]; exact ⟨differentiableAt_const _,by simp [slash,D]⟩
  | add p q hp hq =>
    simp_rw [map_add]; exact ⟨hp.1.add hq.1,by unfold D; rw [fderiv_fun_add hp.1 hq.1]; exact congr_arg₂ (·+·) hp.2 hq.2⟩
  | mul_X p i hp =>
    have hX : (fun x:E4=>here x (X i))= (compAxis i):=funext fun x=> aeval_X ..
    simp_rw [map_mul (here _), Derivation.leibniz, smul_eq_mul, map_add]
    simp_rw [show slash u (X i)=C (u i) from (by simp [slash]), map_mul (here x), show ∀(x:E4), here x (X i)=compAxis i x from congr_fun hX]
    have hi:= (compAxis i).differentiableAt (x:=x)
    refine ⟨hp.1.mul hi,?_⟩; unfold D; rw [fderiv_fun_mul hp.1 hi]
    rw [(compAxis i).fderiv]; change here x p*u i + (compAxis i x)*(D u (fun v=>here v p) x)=_
    simp_rw [hp.2,here,aeval_C,Algebra.algebraMap_self,RingHom.id_apply]

/-- Exists a polynomial after clearing the indicated power of *radius squared*. -/
def rPole (f : E4→ℝ) (s:ℕ): Prop:=∃ p:P, ∀ x≠0, (‖x‖^2)^s*f x=here x p
namespace rPole
lemma bare (a b i l:Axis) : rPole (bareCurl a b i l) 3:= by
  let e (a i : Axis) := C (σ:=Axis) (kr a i)
  refine ⟨C (4 * normal)*(dom*(e a i*e b l-e a l*e b i) -2*(e a i*X b*X l+X a*X i*e b l-e a l*X b*X i-X a*X l*e b i)),?_⟩
  intro x hx
  rw [bare_formula _ _ _ _ hx]; have h : ‖x‖ ≠ 0:= norm_ne_zero_iff.mpr hx
  simp only [wedge,house,houseM,Matrix.of_apply,e, map_sub,map_mul,map_add,map_ofNat,dom_at]
  unfold here; simp only [aeval_C, Algebra.algebraMap_self,RingHom.id_apply,aeval_X]; field_simp; ring
variable {u : E4} {p q : E4→ℝ}
lemma plus (a : rPole p s)(b:rPole q s) : rPole (p+q) s:= by
  obtain ⟨A,hA⟩ := a; obtain ⟨B,hB⟩ := b; exact ⟨A+B,fun x hx=> by rw [Pi.add_apply, map_add, mul_add,hA x hx,hB x hx]⟩
lemma scales (a : rPole p s)(t:ℝ): rPole (t • p) s:= by
  obtain ⟨A,hA⟩:=a; refine ⟨C t*A,fun x hx=>?_⟩
  rw [Pi.smul_apply,smul_eq_mul,map_mul,mul_left_comm, hA x hx]; simp [here]
lemma empty (s:ℕ): rPole 0 s:=⟨0,by simp⟩
lemma replace (h:rPole p s)(he:EqOn p q ({0}ᶜ : Set E4)): rPole q s:=by
  obtain ⟨A,a⟩:=h; exact ⟨A,fun x hx=>by rw [← he hx]; exact a x hx⟩
lemma offset (a:rPole p s)(v:E4)(hp:∀ x≠0,DifferentiableAt ℝ p x): rPole (D v p) (s+1):=by
  obtain ⟨A,h⟩:=a; let N := dom^s; let Q(y:E4):=here y N; let R(y:E4):= ‖y‖^2
  refine ⟨dom*slash v A-C (s:ℝ)*slash v dom*A, fun x hx=>?_⟩
  have he : (Q*p) =ᶠ[𝓝 x] (fun y=>here y A):= by filter_upwards [open_away.mem_nhds (show x∈away from hx)] with y hy; change here y N * p y= _; rw [show here y N=(‖y‖^2)^s by rw [show N=dom^s from rfl,map_pow,dom_at]]; exact h y hy
  have h1 : D v (Q*p) x=here x (slash v A):= (GermD v he).trans (derive (x:=x) v A).2
  have hh : Q= rad s := funext fun y=>by rw [show Q y=(‖y‖^2)^s from map_pow (here y) dom s |>.trans (congr_arg (·^s) (dom_at y))]; rfl
  have hz : rad 1=R:=funext fun i=>by rw [rad,pow_one]
  have h2 : R x* D v Q x= (s:ℝ)*here x (slash v dom)*Q x:= by
    have he := Pole.rad_D s x v; rw [hz] at he
    rw [←(derive v dom).2]; simp_rw [dom_at]; exact hh.symm ▸ he
  have h3:Q x*p x=here x A:= he.self_of_nhds
  have h4:= (derive (x:=x) v N).1
  have he : D v (Q*p) x= Q x*D v p x+p x* D v Q x:= by unfold D; rw [fderiv_mul h4 (hp x hx)]; rfl
  rw [map_sub,map_mul,map_mul,map_mul, show here x (C (s:ℝ))=(s:ℝ) from (by simp [here]),←h1,he, dom_at,← h3]
  change (R x)^(s+1)* D v p x = R x * _ - _ * _
  rw [show (R x)^(s+1)=R x*Q x from ((pow_succ' ..).trans (by rw [hh]; rfl))]; linear_combination -p x * h2
end rPole

variable {u}
lemma formula (p:Probe G j)(q:Probe G 0) : rPole (legKernel p q) (3+j) := by
  induction j with
  | zero =>
    induction p using leg_probe_induction with
    | vars u c i m =>
      induction q using leg_probe_induction with
      | vars v d a b =>
        have h (x : E4)(hx : x≠0) := raw_mixed u v i m a b c d hx
        by_cases hw : c=d
        · apply (rPole.bare i m a b).replace; intro x hx;  change _=(pairing (G:=G) (show x∈away from hx) (constrain (fromF G u c i m))) (constrain (G:=G) (fromF G v d a b)); simpa only [if_pos hw,pow_zero,one_mul, Tensor.coeff_apply_zero] using (h x hx).symm
        apply (rPole.empty _).replace; intro x hx; exact ((h x hx).trans (if_neg hw)).symm
      | zero => exact (rPole.empty _).replace fun x hx=> (map_zero (pairing (G:=G) (show x∈away from hx) _)).symm
      | add p q hp hq => exact (hp.plus hq).replace fun x hx=>(map_add (pairing (G:=G) (show x∈away from hx) _) p q).symm
      | smul a p hp => exact (hp.scales a).replace fun x hx=>(map_smul (pairing (G:=G) (show x∈away from hx) _) a p).symm
    | zero => exact (rPole.empty _).replace fun x hx=> (map_zero ((pairing (G:=G) (show x∈away from hx)).flip q)).symm
    | add p p' hp hq => exact (hp.plus hq).replace fun x hx=>(map_add ((pairing (G:=G) (show x∈away from hx)).flip q) p p').symm
    | smul a p hp => exact (hp.scales a).replace fun x hx=>(map_smul ((pairing (G:=G) (show x∈away from hx)).flip q) a p).symm
  | succ j ih =>
    induction p using leg_probe_induction with
    | vars u c i m =>
      let p:= leg (Fin.tail u) c i m
      let r:ℝ:= ↑(j+1 : ℕ)
      apply ((rPole.offset (ih p) (u 0) fun x hx=>(kernel_smooth p q hx).differentiableAt (by simp)).scales r⁻¹).replace
      intro x hx
      have h:= K_left_D p q (y:=0) (x:=x) (show x≠0 from hx) (u 0); simp only [K,sub_zero] at h
      rw [show raiseLeg _ p=r • leg u c i m by rw [show p=leg _ _ _ _ from rfl, raises, Fin.cons_self_tail]] at h
      change _ = (pairing (G:=G) (show x∈away from hx)).flip q _
      rw [Pi.smul_apply,h,show legKernel (r • _) _ x=r • legKernel _ _ x from map_smul ((pairing (G:=G) (show x∈away from hx)).flip q) r _,smul_smul,inv_mul_cancel₀ (ne_of_gt (by unfold r; positivity)),one_smul]; rfl
    | zero => exact (rPole.empty _).replace fun x hx=> (map_zero ((pairing (G:=G) (show x∈away from hx)).flip q)).symm
    | add p p' hp hq => exact (hp.plus hq).replace fun x hx=>(map_add ((pairing (G:=G) (show x∈away from hx)).flip q) p p').symm
    | smul a p hp => exact (hp.scales a).replace fun x hx=>(map_smul ((pairing (G:=G) (show x∈away from hx)).flip q) a p).symm
end Rad
end YM.PositionX.Rank
