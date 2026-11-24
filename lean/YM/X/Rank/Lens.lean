import YM.X.Rank.Rational
/-!
Univariate extraction of a light-cone pole. Identities throughout on rational germs
on real affine lines. `Shine f c` means has rational continuation to i with value c;
we use this AFTER high enough powers of the vanishing quadratic.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Rank.Rad
open Function Set Filter Polynomial
open scoped BigOperators Classical Topology RealInnerProductSpace Polynomial
variable {G : Gauge}

def Shine (f : ℝ→ℂ)(c:ℂ) := ∃ n d : Polynomial ℂ, d.eval Complex.I≠0 ∧
  (∀ᶠ t:ℝ in atTop,f t * d.eval (t:ℂ)=n.eval (t:ℂ)) ∧ c*d.eval Complex.I=n.eval Complex.I
namespace Shine
variable {f g:ℝ→ℂ}{c z:ℂ}
lemma respects (h:Shine f c)(he:f=ᶠ[atTop] g) : Shine g c:=by
  obtain ⟨n,d,hd,h,hp⟩:=h; exact ⟨n,d,hd,he.mp (h.mono fun t ht h => (show _ * _= _ from h ▸ ht)),hp⟩
lemma poly (p : Polynomial ℂ) : Shine (fun t : ℝ=> p.eval (t:ℂ)) (p.eval Complex.I):= ⟨p,1,by simp,by simp,by simp⟩
lemma const (c:ℂ) : Shine (fun _=>c) c:= by simpa using! poly (C c)
lemma plus (h:Shine f c)(k:Shine g z) : Shine (f+g) (c+z):=by
  obtain ⟨n,d,hd,h,hp⟩:=h; obtain ⟨m,e,he,k,hq⟩:=k; refine ⟨e*n+d*m,d*e,by simpa only [eval_mul] using mul_ne_zero hd he,?_,?_⟩
  · filter_upwards [h,k] with t h k; simp only [eval_add,eval_mul, Pi.add_apply,← h,← k]; ring
  simp only [eval_add,eval_mul,← hp,← hq]; ring
lemma times (h:Shine f c)(k:Shine g z) : Shine (f*g) (c*z):=by
  obtain ⟨n,d,hd,h,hp⟩:=h; obtain ⟨m,e,he,k,hq⟩:=k; refine ⟨n*m,d*e,by simpa only [eval_mul] using mul_ne_zero hd he,?_,?_⟩
  · filter_upwards [h,k] with t h k; simp only [eval_mul, Pi.mul_apply,← h,← k]; ring
  simp only [eval_mul,← hp,← hq]; ring
lemma sum {A:Type*}(s:Finset A){f:A→ℝ→ℂ}{r:A→ℂ}(h:∀ i∈s, Shine (f i) (r i)) : Shine (fun t=> ∑ i∈s,f i t) (∑ i∈s,r i):=by
  induction s using Finset.induction_on with
  | empty => simpa using const (0:ℂ)
  | @insert i s hi ih => simpa only [Finset.sum_insert hi] using! (h i (by simp)).plus (ih (fun j hj=>h j (Finset.mem_insert_of_mem hj)))
lemma powC (p:ℕ)(h:Shine f c): Shine (f^p) (c^p):= by induction p with
  | zero=> simpa only [pow_zero] using! const 1
  | succ p he => rw [pow_succ,pow_succ]; exact he.times h
private lemma eval_equal (p q : Polynomial ℂ)(he:∀ᶠ t:ℝ in atTop,p.eval (t:ℂ)=q.eval (t:ℂ)):p=q:=by
  obtain ⟨r,hr⟩:= eventually_atTop.mp he
  apply Polynomial.eq_of_infinite_eval_eq; apply ((Set.Ioi_infinite r).image (Complex.ofReal_injective.injOn)).mono; rintro x ⟨t,ht,rfl⟩; exact hr t (le_of_lt ht)
lemma separates (h:Shine f c)(he:Shine f z):c=z:=by
  obtain ⟨n,d,hd,h,hp⟩:=h; obtain ⟨m,e,he,k,hq⟩:=he
  have hw:n*e=m*d:=by
    apply eval_equal; filter_upwards [h,k] with t h k; simp only [eval_mul, ←h,←k]; ring
  apply mul_right_cancel₀ (mul_ne_zero hd he : d.eval _ * e.eval _ ≠ 0); rw [← mul_assoc,hp,mul_comm (d.eval _) _,← mul_assoc,hq,← eval_mul, hw, eval_mul]
end Shine

def wire (u v : E4)(i : Axis) : Polynomial ℂ:= C ((↑(u i):ℂ))+X*C ((↑(v i):ℂ))
def visit (u v : E4)(P : P) := MvPolynomial.eval₂Hom (Polynomial.C.comp (algebraMap ℝ ℂ)) (wire u v) P
lemma visit_at (a : ℝ)(P : P)(u v : E4): (visit u v P).eval (a : ℂ)=(here (u+a • v) P:ℂ) := by
  induction P using MvPolynomial.induction_on with
  | C c=> simp [visit,here]
  | add p q hp hq=> unfold visit at *; rw [_root_.map_add,eval_add,map_add (here _),Complex.ofReal_add,hp,hq]
  | mul_X p i hp=> unfold visit at *; rw [map_mul (here _),_root_.map_mul, eval_mul,Complex.ofReal_mul,hp]; simp [here,wire]; exact Or.inl (mul_comm ..)

def beam (u v : E4) : Polynomial ℂ:= C (↑(‖u‖^2):ℂ) + X*C (↑(2 * inner ℝ u v) : ℂ) + X^2*C (↑(‖v‖^2):ℂ)
lemma beam_at (u v:E4)(t:ℝ): (beam u v).eval (t:ℂ)=(↑(‖u+t • v‖^2):ℂ):= by
  simp only [norm_add_sq_real, real_inner_smul_right,norm_smul, beam,Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, eval_pow]
  rw [mul_pow,Real.norm_eq_abs,sq_abs]; push_cast; ring
lemma shine_num {k:ℕ}{f:E4→ℝ}{P:P}(h:∀ x≠0, (‖x‖^2)^k*f x=here x P)(u v:E4)(hv:∀ᶠ t:ℝ in atTop,u+t • v ≠ 0) :
    Shine (fun t:ℝ=> (beam u v|>.eval (t:ℂ))^k * f (u+t • v)) ((visit u v P).eval Complex.I):=by
  apply Shine.respects (Shine.poly (visit u v P)); filter_upwards [hv] with t ht; rw [visit_at,beam_at,← h _ ht]; push_cast; ring
lemma shine_clear {k:ℕ}{f:E4→ℝ}(h:rPole f k) (u v:E4)(hv:∀ᶠ t:ℝ in atTop,u+t • v ≠ 0) (hb:(beam u v).eval Complex.I≠0) : ∃ c:ℂ,
    Shine (fun t:ℝ=> ↑(f (u+t • v))) c := by
  obtain ⟨P,h⟩:=h; let x:ℂ:=(visit u v P).eval Complex.I; let y:ℂ:=(beam u v).eval Complex.I
  refine ⟨x/y^k,visit u v P,beam u v^k,by simpa [eval_pow] using (pow_ne_zero k hb),?_,?_⟩
  · filter_upwards [hv] with t ht; rw [eval_pow,visit_at,beam_at,← h _ ht]; push_cast; ring
  rw [eval_pow]; exact div_mul_cancel₀ _ (pow_ne_zero _ hb)

end YM.PositionX.Rank.Rad
