import YM.X.Rank.PointD
import YM.X.Rank.Strike
/-!
Polynomial coefficients in functional form, before passing the limits of the
middle probe. The pole power at a location is paid **per leg**.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PositionX.Rank
open Function Set Filter Maxwell Wick Maxwell.Free Next.Rank.Normal MvPolynomial Rad
open scoped Topology BigOperators Classical
variable {G : Gauge} {S : Finset E4} {a b m d v u : E4}(c : G.ColorIndex)(h : View S a b m d v)

section lit
abbrev shell (a:E4) (i : Ax 0) : Stroke := (a,⟨0,i⟩)
abbrev penumbra (m v:E4)(w:Flavor 0)(t:ℝ):Scout:=(m-t • v,w)
abbrev glint (d v:E4)(t:ℝ) := (beam d v|>.eval (t:ℂ))^3
abbrev shining (c:G.ColorIndex)(m d v:E4)(w :Flavor 0)(p:Stroke)(t:ℝ):ℂ := glint d v t * pay c (penumbra m v w t) p
abbrev MidOK (S : Finset E4) (a b:E4)(p:Stroke) := p.1∈ S ∨ (p.1=a∨p.1=b)∧ p.2.1=0
lemma lit_f (w : Flavor 0)(u m v:E4)(hv:v≠0)(p : Stroke) (he:p.1-m=u):
    (fun t:ℝ=> pay c (penumbra m v w t) p)=ᶠ[atTop] (fun t=> fare c (ax p.2.1 p.2.2) w (u+t•v)):=by
  filter_upwards [beam_nonzero (u:=u) hv] with t ht; unfold pay; change (if p.1=m-t • v then 0 else fare _ _ _ _) = _; rw [if_neg (show p.1 ≠ _ from ?_)]
  · apply congr_arg; rw [←he]; dsimp only; abel
  intro hq; rw [← he,hq] at ht; apply ht; abel
include h
lemma shimmers (w : Flavor 0) :
    ∃ f:Stroke→ℂ, (∀ i:Stroke,i.1∈ S→ f i=0) ∧ (∀ i:Stroke,MidOK S a b i→ Shine (shining c m d v w i) (f i)):=by
  have hE (p:Stroke)(he:p.1∈ S): Shine (shining c m d v w p) 0:= by
    obtain ⟨x,hx⟩:= shine_clear (f:=fare c (ax p.2.1 p.2.2) w) (formula _ _) (p.1-m) v (beam_nonzero h.hv) (h.offBeam _ he)
    have hP := (Shine.poly (beam d v)).powC 3
    rw [h.onBeam,zero_pow (by decide)] at hP
    have hp := hP.times hx; rw [zero_mul] at hp; apply hp.respects; filter_upwards [lit_f c w _ m v h.hv p rfl] with i hi; change _ * (↑(_:ℝ):ℂ) = _ * (↑(_:ℝ):ℂ); rw [hi]; rfl
  have ht (i:Stroke)(hh:MidOK S a b i): ∃ z, Shine (shining c m d v w i) z:= by
    rcases hh with hh|⟨hh,hk⟩; exact ⟨0,hE i hh⟩
    rcases i with ⟨x,j,p⟩; change (j:ℕ)=0 at hk; subst j; let i:Stroke:=(x,⟨0,p⟩)
    obtain ⟨Q,hQ⟩:= (show rPole (fare c (ax 0 p) w) (3+0) from formula _ _)
    have hp:= shine_num hQ (x-m) v (beam_nonzero h.hv); have hT : beam (x-m) v=beam d v:= by
      cases hh with
      | inl H => rw [show x=a from H,h.h₁]
      | inr H => rw [show x=b from H,h.h₂,beam_eq (beam_iff.mp h.onBeam|>.2)]
    rw [hT] at hp; exact ⟨_,hp.respects ((lit_f c w (x-m) m v h.hv i rfl).mono (fun t ht=> congr_arg (fun y:ℝ=>glint d v t*y) ht.symm))⟩
  choose! z hz using ht; refine ⟨z,fun i hi=> ?_,hz⟩
  exact (hz i (Or.inl hi)).separates (hE i hi)
omit h
lemma scaled_row (k:G.ColorIndex)(w:Flavor 0)(f:Stroke→ℂ)(z:Fiber G) (hk:Shine (shining c m d v w z.1) (f z.1)) :
    Shine (fun t=> (glint d v t • cost c k (penumbra m v w t)) z) (dip f k z):= by
  by_cases hx:z.2=k
  · simpa only [smul_eq_mul,Pi.smul_apply,cost,dip,hx,↓reduceIte] using! hk
  simpa only [Pi.smul_apply,smul_eq_mul,cost,dip,if_neg hx,mul_zero] using! Shine.const 0
lemma scaled_bill (c:G.ColorIndex)(m d v:E4)(w:Flavor 0)(f:Stroke→ℂ)(z:Scout) (hk:∀ i:Ax 0, Shine (shining c m d v w (shell z.1 i)) (f (shell z.1 i))) :
    Shine (fun t=>glint d v t* hot c z (penumbra m v w t)) (bill z.1 z.2 f):= by
  simp_rw [← bill_pay c, bill, Finset.mul_sum]; refine Shine.sum _ fun i _=> ?_
  simp_rw [mul_left_comm (glint ..)]; exact (Shine.const _).times (hk i)
lemma cash_linear (f:Stroke→ℂ)(a:E4): ∃ L:Flavor 0→ₗ[ℝ]ℂ,(bill a · f)=⇑L:= by
  let L (i:Ax 0):=(LinearMap.toSpanSingleton ℝ ℂ (f (shell a i))).comp ((ax 0).coord i)
  refine ⟨∑ i,L i,funext fun q=>?_⟩
  rw [LinearMap.sum_apply]; unfold bill; apply Finset.sum_congr rfl; intro i _; exact (Complex.real_smul ..).symm
end lit

section generic
variable {V : Type*} (y : V→ℂ)
lemma slit_congr (f : poly V)(S : Set V)(hs : f ∈ supported ℂ S){z : V→ℂ}(hz:EqOn y z S) : slit y f=slit z f:= derivation_eqOn_supported (fun i hi=> by simp only [comp_apply]; rw [slit_X,slit_X,hz hi]) hs
lemma slit_rename {U:Type*}(f: V→ U)(x:poly V)(y:U→ℂ): slit y (rename f x)=rename f (slit (y∘ f) x):= by
  rw [labelled]
  rw [exchange_slit,show reads (fun i=>Finsupp.single (f i) 1) y=y∘ f from (funext fun i=>by simp [reads])]
lemma slit_stays {p:poly V}{S:Set V}(h:p∈ supported ℂ S) : slit y p∈supported ℂ S := by
  rw [supported_eq_range_rename] at *; obtain ⟨q,rfl⟩:=h; exact ⟨_, (slit_rename ..).symm⟩
lemma slit_single (t:V)(p:poly V): slit (Pi.single t 1) p=pderiv t p := by
  apply MvPolynomial.derivation_eq_of_forall_mem_vars; intro i _; rw [slit_X,pderiv_X]; by_cases ht:t=i <;> simp [ht,Ne.symm]
lemma slit_flat (t:Finset V)(p:poly V)(hs:p.vars⊆ t): slit y p= ∑ v∈t,y v • pderiv v p := by
  let q:=∑ v∈t,y v • Pi.single v 1
  rw [slit_congr y p (t:Set V) (mem_supported.mpr (by exact_mod_cast hs)) (show EqOn y q _ from ?_)]
  · unfold q;rw [slit_total]; simp_rw [slit_smul,slit_single]
  intro i hi; unfold q; simp [Finset.sum_apply,Pi.single_apply, (show i∈t from hi)]
lemma twice_limit (f : ℝ→V→ℂ)(L: poly V →ₗ[ℂ] ℂ)(p:poly V)(h: ∀ i∈ p.vars, Shine (fun t=>f t i) (y i)) :
    Shine (fun t=> L (slit (f t) (slit (f t) p))) (L (slit y (slit y p))) := by
  simp_rw [slit_flat y p.vars p le_rfl,fun t=>slit_flat (f t) p.vars p le_rfl,map_sum,Derivation.map_smul,map_smul]
  refine Shine.sum (p.vars) fun i hi=> ?_
  let q:=pderiv i p; have hq:q.vars⊆p.vars:= by
    rw [← show slit _ _= q from slit_single i p]; exact mem_supported.mp (slit_stays (Pi.single i 1) p.mem_supported_vars)
  suffices he: Shine (fun t=> L (slit (f t) q)) (L (slit y q)) from (h _ hi).times he
  simp_rw [slit_flat y p.vars q hq,fun t=>slit_flat (f t) p.vars q hq,map_sum,map_smul]
  exact Shine.sum _ fun k hk=> (h k hk).times (Shine.const _)
end generic
end YM.PositionX.Rank
