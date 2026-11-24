import YM.XSpace.Snow

/-! # Payment over the Gram ball as pair Laplacian costs -/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Snow
open Function Set Filter MeasureTheory Lap Legs
open MvPolynomial Next.Rank.Normal
open scoped BigOperators Topology RealInnerProductSpace ContDiff Classical
variable {F ι : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable [FiniteDimensional ℝ F] [MeasureSpace F] [BorelSpace F] [Measure.IsAddHaarMeasure (volume : Measure F)]
variable (r : ℝ) (V : ι→F) (n : ℕ) (S : Finset ι)

def eyes (x : F): poly ι→ₐ[ℂ] ℂ:= aeval fun i=> (⟪V i,x⟫:ℂ)
def grams : Symmetric ι:= ⟨fun i j=> (⟪V j,V i⟫:ℂ),fun i j=> by rw [real_inner_comm]⟩
omit [FiniteDimensional ℝ F] [MeasureSpace F] [BorelSpace F] [Measure.IsAddHaarMeasure (volume : Measure F)] in
lemma looks (p : poly ι) : ContDiff ℝ 1 (fun x=> eyes V x p):=by
  induction p using MvPolynomial.induction_on with
  | C a=>simpa [eyes] using (contDiff_const (c:=a) (n:=1) (𝕜:=ℝ) (E:=F))
  | add p q hp hq=>simp only [map_add]; exact hp.add hq
  | mul_X p i hp=>simp only [map_mul,eyes,aeval_X]; exact hp.mul (Complex.ofRealCLM.contDiff.comp (innerSL ℝ (V i)).contDiff)

lemma finiteEyes (p : poly ι): Integrable (fun x => point r n x • eyes V x p):= finite r n _ (looks V p).continuous

def credit : poly ι →ₗ[ℂ] ℂ where
  toFun p:= ∫ x, point r n x • eyes V x p
  map_add' p q:=by simp_rw [_root_.map_add,smul_add]; rw [integral_add (finiteEyes r V n p) (finiteEyes r V n q)]
  map_smul' z p:=by simp_rw [map_smul,smul_comm _ z]; exact integral_smul ..

omit [FiniteDimensional ℝ F] [MeasureSpace F] [BorelSpace F] [Measure.IsAddHaarMeasure (volume : Measure F)] in
lemma gaze (x:F) (p : poly ι) (i:ι): fderiv ℝ (fun y=> eyes V y p) x (V i)=eyes V x (first (grams V) i p):=by
  induction p using MvPolynomial.induction_on with
  | C a=> simp [first,eyes]
  | add p q hp hq=> simp only [_root_.map_add,first]; rw [fderiv_fun_add ((looks _ p).differentiable (by simp) _) ((looks _ q).differentiable (by simp) _), add_apply, hp,hq]
  | mul_X p j hp=>
    rw [mul_comm p]; let L:= (Complex.ofRealCLM).comp (innerSL ℝ (V j)); have he t : eyes V t (X j)=L t:=aeval_X ..; simp_rw [_root_.map_mul (eyes ..),he]; rw [fderiv_fun_mul L.differentiableAt ((looks V p).differentiable (by simp) _),L.fderiv]; unfold first; rw [slit_prod,map_add,map_mul,map_mul, add_apply, smul_apply,smul_apply,hp]; rw [smul_eq_mul,smul_eq_mul, he, mul_comm (eyes V x p)]; congr 2; simp [eyes]; rfl

lemma bank (i : ι) (p : poly ι): credit r V (n+1) (first (grams V) i p)= coeff n • credit r V n (X i*p):=by
  have he:=ibp r n (fun x=>eyes V x p) (looks V p) (V i); simp_rw [gaze] at he; simpa only [credit, LinearMap.coe_mk, AddHom.coe_mk,map_mul,eyes, aeval_X, Complex.real_smul] using he

variable {p : poly ι}

-- price using recursion only by heights. No formal series theorem needed.
variable (F) in
def weight (n i : ℕ):ℂ:=
  match i with
  | 0=> ((∫ x:F, point r n x):ℂ)
  | i+1 => ((coeff n:ℂ)* (2*(i+1:ℕ)))⁻¹*weight (n+1) i
omit [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [BorelSpace F] [Measure.IsAddHaarMeasure (volume : Measure F)] in
private lemma w_move (i : ℕ): (coeff n:ℂ)*weight F r n (i+1)*(2*(i+1:ℕ))=weight F r (n+1) i:=by
  rw [weight]; have ht: (coeff n:ℂ)≠0:=by unfold coeff; exact_mod_cast (by positivity : (2:ℝ)*(n+2:ℕ)≠0)
  field_simp

def accolade (m : ℕ): poly ι→ₗ[ℂ]ℂ:= (aeval (0:ι→ℂ)).toLinearMap ∘ₗ (∑ i∈Finset.range m, weight F r n i • (Lap.op S (grams V))^i)
omit [FiniteDimensional ℝ F] [BorelSpace F] [Measure.IsAddHaarMeasure (volume : Measure F)] in
lemma h_score (m : ℕ) (p : poly ι): accolade r V n S m p=∑ i∈Finset.range m, weight F r n i • aeval (0:ι→ℂ) (((Lap.op S (grams V))^i) p):=by unfold accolade; simp only [LinearMap.comp_apply,LinearMap.sum_apply,LinearMap.smul_apply,map_sum,map_smul]; rfl
omit [FiniteDimensional ℝ F] [BorelSpace F] [Measure.IsAddHaarMeasure (volume : Measure F)] in
private lemma lights (m : ℕ) {i : ι} (hi:i∈S) (h:p ∈ Lap.scope S):
    accolade r V (n+1) S m (first (grams V) i p)= coeff n • accolade r V n S (m+1) (X i*p):=by
  let D:= Lap.op S (grams V); let R:= slit ((grams V).cov i)
  rw [h_score,h_score,Finset.sum_range_succ']; simp_rw [Lap.op_j_pow S (grams V) hi h, map_add,map_mul,aeval_X, Pi.zero_apply,zero_mul,zero_add, pow_zero,Module.End.one_apply,map_smul];
  -- simplify
  simp only [map_mul, aeval_X, Pi.zero_apply, zero_mul,smul_zero,add_zero]; rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro k _
  have he (z): ((D^z) (R p))=R ((D^z) p):=by
    induction z with
    | zero=> rfl
    | succ z ih=> rw [pow_succ']; change D _ = R (D _); rw [ih,Lap.op_data]
  rw [show (D^k) (first (grams V) i p)=_ from he k]; simp only [Complex.real_smul,smul_eq_mul]; rw [← mul_assoc, ← mul_assoc,w_move]


private def Dry : Submodule ℂ (poly ι) where
  carrier:= setOf fun p=> ∀ n,∀ᶠ m in atTop, credit r V n p=accolade r V n S m p
  zero_mem':= fun n =>by simp
  add_mem':=by intro p q h j n; filter_upwards [h n,j n] with m hm hv; simp only [map_add,hm,hv]
  smul_mem':=by intro z p h n; filter_upwards [h n] with m hm; simp only [map_smul,hm]
private def Whole (k : ℕ): Submodule ℂ (poly ι) := match k with
  | 0=> Dry r V S
  | i+1=> ⨅ f:ι→ℂ, (Whole i).comap (slit f).toLinearMap
private def Everywhere:= ⨅ k:ℕ, Whole r V S k
private lemma dry_at (hp:p∈Everywhere r V S) (n:ℕ): ∀ᶠ m in atTop,credit r V n p=accolade r V n S m p:= (show p∈Dry r V S from (show Everywhere r V S ≤ Whole r V S 0 from iInf_le ..) hp) n
private lemma ice_c (a :ℂ) : C a∈Everywhere r V S:= by
  rw [Everywhere,Submodule.mem_iInf]; intro n; cases n with
  | zero =>
    intro k; filter_upwards [eventually_gt_atTop 0] with m hm
    obtain ⟨m,rfl⟩:=Nat.exists_eq_succ_of_ne_zero hm.ne'
    rw [h_score, Finset.sum_range_succ']; have he i : ((Lap.op S (grams V))^(i+1)) (C a)=0:=by rw [pow_succ]; simp [Module.End.mul_apply,op_at]
    simp only [he,map_zero,smul_zero,Finset.sum_const_zero,zero_add,pow_zero,Module.End.one_apply]; simp [credit,eyes,weight,Complex.real_smul,integral_mul_const]
  | succ n=> rw [Whole,Submodule.mem_iInf]; intro f; rw [Submodule.mem_comap]; exact (slit_C f a).symm ▸ Submodule.zero_mem _
private lemma Everywhere.multiply (hp:p∈Everywhere r V S) (h:p∈Lap.scope S) (i:ι) (hi:i∈S): X i*p∈Everywhere r V S:= by
  unfold Everywhere at *; rw [Submodule.mem_iInf]; intro k
  induction k generalizing p with
  | zero=>
    intro k; have he : first (grams V) i p∈ Everywhere r V S:= by
      unfold Everywhere; rw [Submodule.mem_iInf]; intro k; exact (show ∀ f:ι→ℂ,slit f p∈Whole r V S k from fun f=> (show Whole r V S (k+1) ≤ (Whole r V S k).comap (slit f).toLinearMap from iInf_le ..) ((iInf_le (Whole r V S) (k+1)) hp)) _
    obtain ⟨m,hm⟩:=eventually_atTop.mp (dry_at r V S he (k+1))
    filter_upwards [eventually_gt_atTop m] with l hl; obtain ⟨j,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (show l≠0 by omega)
    apply smul_right_injective ℂ (by unfold Snow.coeff; positivity : coeff k≠0); change coeff k • _ = coeff k • accolade r V k S (j+1) (X i*p); rw [← bank,← lights (p:=p) _ _ _ _ _ hi h,hm j (by omega)]
  | succ k ih=>
    rw [Whole,Submodule.mem_iInf]; intro f; change slit f (X i*p) ∈ Whole r V S k; rw [slit_prod,C_mul']; apply Submodule.add_mem _ (ih ?_ (split_in _ _ h)) (Submodule.smul_mem _ _ ((iInf_le (Whole r V S) k) hp)); rw [Submodule.mem_iInf]; intro j; exact (show Whole r V S (j+1)≤ (Whole r V S j).comap (slit f).toLinearMap from iInf_le ..) ((iInf_le (Whole r V S) (j+1)) hp)
lemma credit_agrees (h : p ∈ Lap.scope S) : ∀ᶠ m in atTop, credit r V n p=accolade r V n S m p:=by
  apply dry_at; rw [Lap.scope,supported_eq_range_rename] at h; rw [AlgHom.mem_range] at h; obtain ⟨P,rfl⟩:=h
  induction P using MvPolynomial.induction_on with
  | C a=> rw [rename_C]; exact ice_c r V S a
  | add p q hp hq=> rw [map_add]; exact Submodule.add_mem _ hp hq
  | mul_X p i hp=> rw [mul_comm p,map_mul,rename_X]; apply Everywhere.multiply r V S hp _ _ i.property; rw [Lap.scope,supported_eq_range_rename]; exact AlgHom.mem_range_self ..
end YM.XSpace.Snow
