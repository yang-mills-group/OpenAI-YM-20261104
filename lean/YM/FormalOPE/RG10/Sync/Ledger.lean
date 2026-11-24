import YM.FormalOPE.RG10.Sync.Gaussian
import Mathlib.Algebra.MvPolynomial.Funext
/-!
 # Coding real Ticket formal weights on field variables into actual polynomial budget ring
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Sync
open Filter Topology MeasureTheory Function
open PertExtension.GaussianScore MultiGauge MultiGauge.Splice MultiGauge.Papers
open YM.Multi.Vacuum.Gauss
open Route MvPolynomial
open scoped Classical ContDiff Topology BigOperators ENNReal
variable {I:Type}[Fintype I]
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
-- use any layout. Certified canonical layouts can choose OEdge×Color
abbrev Layout (I E:Type)[NormedAddCommGroup E][NormedSpace ℝ E]:= E≃ₗ[ℝ] Row I
variable (L:Layout I E)
 def tint (x:E)(i:I): ℂ := L x i
 def Realised (p:Packet I)(A:E→ℝ):Prop:= ∀ x:E, aeval (tint L x) p= Complex.ofReal (A x)
 def stroke (f:Module.Dual ℝ E): Packet I:= let B:= Module.Basis.ofEquivFun L; ∑ i, MvPolynomial.C (Complex.ofReal (f (B i))) * MvPolynomial.X i
lemma stencil (f:Module.Dual ℝ E): Realised L (stroke L f) f:= by
 intro x; let B:= Module.Basis.ofEquivFun L; unfold stroke; simp only [_root_.map_sum, map_mul, aeval_C,aeval_X, tint]
 rw [show f x=∑ i, f (B i)*L x i from ?_,Complex.ofReal_sum]; simp_rw [Complex.ofReal_mul]; rfl
 conv_lhs=> rhs; rw [← L.symm_apply_apply x]; lhs; rw [←Module.Basis.equivFun_ofEquivFun L]; -- try
 rw [Module.Basis.equivFun_symm_apply, _root_.map_sum]; simp [B,mul_comm]
lemma credible (p:Permit E): ∃ q:Packet I, Realised L q p.val:= by
 refine Papers.induction (P:=fun f:E→ℝ=>∃ q:Packet I, Realised L q f) (fun ℓ=>⟨_,stencil L ℓ⟩) (fun x=> ⟨C (Complex.ofReal x),fun _=> aeval_C ..⟩) ?_ ?_ p.property
 · rintro _ _ _ _ ⟨u,h⟩ ⟨v,k⟩; exact ⟨u+v,fun x=> by rw [map_add,h,k, Pi.add_apply,Complex.ofReal_add]⟩
 rintro _ _ _ _ ⟨u,h⟩ ⟨v,k⟩; exact ⟨u*v,fun x=> by rw [map_mul,h,k, Pi.mul_apply,Complex.ofReal_mul]⟩
omit [Fintype I] in
lemma recognise {a b:Packet I}(h:∀ x:E, aeval (tint L x) a=aeval (tint L x) b): a=b:= by
 apply MvPolynomial.funext_set (p:=a) (fun _=> Set.range Complex.ofReal) (fun _=> Set.infinite_range_of_injective Complex.ofReal_injective)
 intro y hy
 have he i: Complex.ofReal (y i).re= y i:= by obtain ⟨a,h⟩:= hy i (Set.mem_univ i); simp [← h]
 specialize h (L.symm (fun i=>(y i).re)); rw [show tint L (L.symm (fun i=>(y i).re))=y from _root_.funext (fun i=> by simp [tint,he])] at h
 simpa using h

 def ink : Permit E →+* Packet I where
  toFun a:= (credible L a).choose
  map_mul' a b:= recognise L fun x=> by rw [map_mul,(credible L a).choose_spec x,(credible L b).choose_spec x,(credible L (a*b)).choose_spec x]; exact Complex.ofReal_mul ..
  map_add' a b:= recognise L fun x=> by rw [map_add,(credible L a).choose_spec x,(credible L b).choose_spec x,(credible L (a+b)).choose_spec x]; exact Complex.ofReal_add ..
  map_one':= recognise L fun x=> by rw [(credible L (1:Permit E)).choose_spec x,map_one]; rfl
  map_zero':= recognise L fun x=> by rw [(credible L (0:Permit E)).choose_spec x,map_zero]; rfl
lemma expresses (a:Permit E): Realised L (ink L a) a.val:= (credible L a).choose_spec
omit [Fintype I] in
lemma identityLaw {a:Permit E}{p q:Packet I}(h:Realised L p a.val)(u:Realised L q a.val): p=q:= recognise L fun x=> (h x).trans (u x).symm
open PowerSeries
 def digital : Ticket E→+* Channel I := PowerSeries.map (ink L)
 def align : PowerSeries ℝ →+* RG10.Series:= PowerSeries.map Complex.ofRealHom
lemma currency (x:ℝ): ink L (algebraMap ℝ (Permit E) x)= MvPolynomial.C (x:ℂ):= recognise L fun i=> by rw [expresses,MvPolynomial.aeval_C]; rfl
lemma accessing (A:Ticket E)(x:E): run (tint L x) (digital L A) = align (Stack.read x A):= by
 apply PowerSeries.ext; intro i; rw [run_charge,digital,PowerSeries.coeff_map,align,PowerSeries.coeff_map,expresses,Stack.reading_term]; rfl
omit [Fintype I] in
lemma discriminating {u v:Channel I}(h:∀ x:E,run (tint L x) u=run (tint L x) v): u=v:=PowerSeries.ext fun i=> recognise L (fun x=> by rw [←run_charge,←run_charge,h x])
lemma sendoff (f:Module.Dual ℝ E): digital L (PowerSeries.C (⟨f,linear _⟩))= PowerSeries.C (stroke L f):= by
 rw [digital,PowerSeries.map_C,identityLaw L (expresses L ⟨f,linear _⟩) (stencil L f)]
end YM.FormalOPE.RG10.Sync
