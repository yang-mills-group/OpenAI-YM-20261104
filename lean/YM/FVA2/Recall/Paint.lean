import YM.FVA2.Recall.Lift
/-!
 # Polynomial substitution of logarithmic frame scale (same series for every coefficient)

 For genuine Ticket polynomial coefficients with no extra finiteness statement
 about degrees *across* perturbative orders. The scaling itself has order-dependent
 coordinates. Avoid nilpotent scalar assignments to linear-combination marks.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Recall.Paint
open Function Set Filter Finset MeasureTheory FormalOPE.RG10 FormalOPE.RG10.MultiGauge
open StationaryMarks MultiGauge.Stack PowerSeries MarkovChain Warp Splice
open scoped Topology ContDiff BigOperators Classical
variable {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
-- not requiring FD for purely polynomial statements

def mirror (w:Polynomial (Permit E)) (x:E): Polynomial ℝ:= w.map (Stack.reading x).toRingHom
@[simp] lemma mirror_c (v:Permit E)(x:E): mirror (Polynomial.C v) x=Polynomial.C (v.val x):= Polynomial.map_C (Stack.reading x).toRingHom
lemma free (p q: Polynomial (Permit E))(h:∀ (x:E)(z:ℝ),(mirror p x).eval z=(mirror q x).eval z): p=q:= by
 apply Polynomial.ext; intro v; apply Subtype.ext; funext x; obtain ht:= Polynomial.funext (h x); have hv:= congr_arg (fun p:Polynomial ℝ=> p.coeff v) ht; unfold mirror at hv; simp_rw [Polynomial.coeff_map] at hv; exact hv

abbrev stamp (t:E→ℝ) (P:Polynomial (Permit E)):= ∀ (x:E)(z:ℝ), (mirror P x).eval z=t (z • x)
lemma stamp_add {a b:E→ℝ}{v w:Polynomial (Permit E)}(h:stamp a v)(k:stamp b w): stamp (a+b) (v+w):= by
 intro x z; unfold mirror; rw [Polynomial.map_add,Polynomial.eval_add]; exact congr_arg₂ (· + ·) (h x z) (k x z)
lemma stamp_mul {a b:E→ℝ}{v w:Polynomial (Permit E)}(h:stamp a v)(k:stamp b w): stamp (a*b) (v*w):= by intro x z; unfold mirror; rw [Polynomial.map_mul, Polynomial.eval_mul]; exact congr_arg₂ (· * ·) (h x z) (k x z)

abbrev constant (p:ℝ) : Permit E := algebraMap _ _ p
abbrev element (u:Module.Dual ℝ E) : Permit E:= ⟨u,Papers.linear u⟩
lemma permitted (v:Permit E):∃ p, stamp v.val p:= by
 apply Papers.induction (P:=fun t:E→ℝ=>∃ p,stamp t p) _ _ _ _ v.property
 · refine fun u=>⟨ Polynomial.X * Polynomial.C (element u),fun x z=> ?_⟩; unfold mirror; simp only [Polynomial.map_mul,Polynomial.map_C,Polynomial.map_X,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_C,map_smul]; rfl
 · refine fun x=> ⟨Polynomial.C (constant x),?_⟩; intro i y; rw [mirror_c, Polynomial.eval_C]; rfl
 · rintro _ _ _ _ ⟨p,hp⟩ ⟨v,hv⟩; exact ⟨p+v,stamp_add hp hv⟩
 rintro _ _ _ _ ⟨p,hp⟩ ⟨v,hv⟩; exact ⟨p*v, stamp_mul hp hv⟩

private def portrait' (v:Permit E):= (permitted v).choose
private lemma posted' (v:Permit E)(w:Polynomial (Permit E))(h:stamp v.val w): portrait' v=w:= free _ _ (fun x z=> ((permitted v).choose_spec x z).trans (h x z).symm)

def Values (p:Permit E)(n:ℕ) : Prop:=∀ (x:E)(z:ℝ), p.val (z • x)=z^n * p.val x
lemma tint' (p:Permit E){n:ℕ}(h:Values p n): portrait' p = Polynomial.X^n*Polynomial.C p:= posted' p _ (fun x z=> by unfold mirror; rw [Polynomial.map_mul,Polynomial.map_C, Polynomial.map_pow,Polynomial.map_X,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_C]; exact (h x z).symm)
lemma stasis (r:ℝ): Values (E:=E) (constant r) 0:= fun _ _=> by rw [pow_zero,one_mul];rfl

def portrait (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E]: Permit E →+* Polynomial (Permit E) where
 toFun:=portrait'
 map_one':= by rw [← map_one (algebraMap ℝ (Permit E)), tint' (constant _) (stasis 1), pow_zero]; unfold constant; simp
 map_zero':= by rw [← map_zero (algebraMap ℝ (Permit E)), tint' (constant _) (stasis 0), pow_zero]; unfold constant; simp
 map_add' a b:=posted' (a+b) _ (stamp_add (permitted a).choose_spec (permitted b).choose_spec)
 map_mul' a b:=posted' (a*b) _ (stamp_mul (permitted a).choose_spec (permitted b).choose_spec)
lemma portrait_home (p:Permit E)(x:E)(z:ℝ) : ( mirror ( portrait E p ) x ).eval z=p.val (z • x):= (permitted p).choose_spec x z
-- homogeneous dynamics. polarization only along scalar t
lemma covers (u: Permit E): u∈ Submodule.span ℝ { v:Permit E|∃ i,Values v i}:= by
 let V:Set (Permit E):= {v|∃ i, Values v i}; let B:= Submodule.span ℝ V
 let P (x:E→ℝ):=∃ s∈B,s.val=x
 have hm:= show P u.val from (by
    apply Papers.induction (P:=P) _ _ _ _ u.property
    · exact fun v=> ⟨element v, Submodule.subset_span (show element v∈V from ⟨1,fun x z=>by change v (z • x)= _; rw [pow_one,map_smul]; rfl⟩ ), rfl ⟩
    · exact fun x=> ⟨constant x, Submodule.subset_span (show _∈V from ⟨_,stasis x⟩),rfl⟩
    · rintro _ _ _ _ ⟨p,h,rfl⟩ ⟨q,hq,rfl⟩; exact ⟨p+q,B.add_mem h hq,rfl⟩
    rintro _ _ _ _ ⟨p,h,rfl⟩ ⟨q,hq,rfl⟩; refine ⟨p*q,?_,rfl⟩; apply LinearMap.BilinMap.apply_apply_mem_of_mem_span B V V (LinearMap.mul ℝ (Permit E)) _ p q h hq -- arguments
    rintro a ⟨k,hk⟩ b ⟨l,hl⟩; refine Submodule.subset_span (show a*b∈V from ⟨ k+l, fun x z=>?_⟩); change a.val _ * b.val _= _ * (a.val x*b.val x); rw [hk,hl,pow_add]; ring )
 obtain ⟨x,hk,hx⟩:=hm; exact Subtype.ext hx ▸ hk

variable (r:PowerSeries ℝ)
-- polynomial extension along procedural read y

def service (E:Type) [NormedAddCommGroup E][NormedSpace ℝ E] : Permit E →+* Ticket E:= (Polynomial.eval₂RingHom C (carry r)).comp (portrait E)
lemma service_value (p:Permit E){i:ℕ}(h:Values p i): service r E p= carry r^i * C p:= by
 unfold service; rw [ RingHom.comp_apply,show portrait E p= _ from tint' p h]; simp only [map_mul,map_pow, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,Polynomial.eval₂_C]; -- ambiguity map_pow priority
lemma fixed_g (z:ℝ): service r E (constant z) = roll z:= by rw [service_value r _ (stasis _), pow_zero, one_mul]; rfl
lemma flash (z:ℝ)(f:Permit E): z • f=constant z * f:= by apply Subtype.ext; rfl

-- commute linear maps, stepwise
lemma unsigned (T:F→ₗ[ℝ] E)(w:PowerSeries ℝ): boost T (carry w)= carry w := by apply Stack.into; intro x; simp_rw [caught,load]
lemma calm (T:F→ₗ[ℝ] E)(w: Permit E): boost T (service r E w)= service r F (Papers.translation T w):= by
 let H:= Papers.translation T
 induction covers w using Submodule.span_induction with
 | mem v h=>
    obtain ⟨i,h⟩:= h
    have he: Values (H v) i:= fun x z=> by change v.val ( T (z • x))=_; rw [map_smul];exact h _ _
    rw [ service_value r v h,_root_.map_mul, _root_.map_pow,unsigned, service_value r (H v) he ] -- boost C
    rw [show boost T (C v)= C ( Papers.translation T v ) from PowerSeries.map_C ..]
 | zero=> simp
 | add=> rename_i ia ib; simp only [_root_.map_add,ia,ib]
 | smul=> rename_i c v h hv; rw [map_smul H]; simp_rw [flash, _root_.map_mul, fixed_g, OpenSlots.boost_c, hv]; rfl
end YM.FVA2.Recall.Paint
