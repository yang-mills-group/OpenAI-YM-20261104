import YM.FVA2.Recall.Paint
/-!
 # Actual full parameter/frame scaling homomorphism used to compare tickets
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Recall
open Function Set Filter Finset MeasureTheory FormalOPE.RG10 FormalOPE.RG10.MultiGauge
open StationaryMarks MultiGauge.Stack PowerSeries MarkovChain Warp Splice OpenSlots
open Paint PertExtension PertExtension.Series Radial GaussianScore
open scoped Classical Topology BigOperators ContDiff
variable {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]

structure Move where
 path : PowerSeries ℝ
 starts : PowerSeries.constantCoeff path=1
variable (m:Move)
namespace Move
abbrev p := m.path
abbrev q := m.path⁻¹
/-- Original common coupling in new common coupling units. All history weights must change. -/
def frame := X * m.p
local notation "r"=> Move.frame m
lemma old : m.p*m.q=1:= PowerSeries.mul_inv_cancel _ (fun h=> one_ne_zero (m.starts.symm.trans h))
lemma initial : constantCoeff m.q=1:= by obtain h:=congr_arg constantCoeff m.old; rw [map_mul,map_one,show constantCoeff m.p=1 from m.starts,one_mul] at h; exact h
lemma grounded : constantCoeff m.frame=0:= by simp [frame]

def sponsor : PowerSeries ℝ →+* PowerSeries ℝ:= Porch.trip C m.p
lemma sponsor_neat : Neat (sponsor m):= Porch.trip_neat C m.p
@[simp] lemma sponsor_c (x:ℝ): m.sponsor (C x)= C x:= Porch.fromC ..
@[simp] lemma sponsor_x : m.sponsor X=m.frame:= Porch.source ..
lemma permits : PowerSeries.HasSubst (S:=ℝ) (frame m):= .of_constantCoeff_zero' m.grounded
-- public relation with external witnesses using library subst
lemma frame_stamp (v:PowerSeries ℝ): m.sponsor v= v.subst (frame m):= by
 apply PowerSeries.ext; intro k; rw [PowerSeries.coeff_subst' m.permits, finsum_eq_finsetSum_of_support_subset (s:=Finset.range (k+1))] -- lemma name
 · change coeff k (Porch.run C m.p v)=_; simp only [Porch.run, AddMonoidHom.coe_mk, ZeroHom.coe_mk, coeff_mk]; apply Finset.sum_congr rfl; intro i _; rw [coeff_mul_C,mul_comm]; rfl
 intro i hi; by_contra! H; refine hi ?_; change (coeff i v) • (coeff k ((X*m.p)^i))=0; rw [mul_pow,coeff_X_pow_mul',if_neg (by simp at H; omega),smul_zero]

def walk (E:Type) [NormedAddCommGroup E][NormedSpace ℝ E] : Ticket E →+* Ticket E:= Porch.trip (service m.q E) (carry m.p)
local notation "Φ"=> Move.walk m E
local notation "Λ"=> Move.walk m F
local notation "Ψ"=> m.sponsor
lemma neat : Neat (Φ):= Porch.trip_neat (service m.q E) (carry m.p)
@[simp] lemma walk_c (f:Permit E): Φ (C f)=service m.q E f:= Porch.fromC ..
@[simp] lemma walk_x : Φ X=X*carry m.p:= Porch.source ..
@[simp] lemma fix (v:ℝ): Φ (roll v)=roll v:= by change Φ ( C (constant v))= _; rw [walk_c,fixed_g]
lemma boots (T:F→ₗ[ℝ] E)(A:Ticket E): Λ (boost T A) = boost T (Φ A):= by
 refine ( recruit ((Λ).comp (boost T)).toAddMonoidHom ((boost T).comp (Φ)).toAddMonoidHom (fun a=> m.neat (neatC (Papers.translation T).toRingHom a)) (fun h=> neatC (Papers.translation T).toRingHom (m.neat h)) ?_ A )
 intro k v; change Λ (boost T _) = boost T (Φ _); simp_rw [_root_.map_mul, _root_.map_pow,show ∀ u, boost T (C u)= C (Papers.translation T u) from fun u=> PowerSeries.map_C .., show boost T X=X from PowerSeries.map_X ..,walk_x,walk_c, Paint.calm, _root_.map_mul, unsigned]; rw [show boost T X=X from PowerSeries.map_X ..]
lemma carries (v:PowerSeries ℝ): Φ (carry v)=carry (Ψ v):= by
 refine recruit ( (Φ).comp carry ).toAddMonoidHom (carry.comp Ψ).toAddMonoidHom (fun h=>m.neat (neatC (algebraMap ℝ (Permit E)) h)) (fun h=> neatC (algebraMap ℝ (Permit E)) (m.sponsor_neat h)) ?_ v
 intro k u; change Φ (carry _) = carry (Ψ _); simp_rw [_root_.map_mul,_root_.map_pow, sponsor_x, sponsor_c,show ∀ u, (carry (C u):Ticket E)= roll u from fun u=>PowerSeries.map_C ..,frame, _root_.map_mul, show (carry (E:=E) X)=X from PowerSeries.map_X ..,walk_x,fix]
lemma service_lead (v:Permit E): constantCoeff (service m.q E v)=v:= by
 induction Paint.covers v using Submodule.span_induction with
 | mem x h=> obtain ⟨i,h⟩:=h; rw [service_value _ x h,map_mul,map_pow, constantCoeff_C]; unfold carry; rw [ ← coeff_zero_eq_constantCoeff_apply,PowerSeries.coeff_map,coeff_zero_eq_constantCoeff_apply,m.initial,map_one,one_pow,one_mul]
 | zero=> simp
 | add=> rename_i h k; simp only [map_add,h,k]
 | smul=> rename_i x i _ hi; rw [flash]; simp_rw [ _root_.map_mul, fixed_g, roll,constantCoeff_C,hi]
lemma constantLead (p:Ticket E): constantCoeff (Φ p)= constantCoeff p:= by
 have he:Through 0 p (C (constantCoeff p)):= by intro i hi; cases le_antisymm hi (Nat.zero_le i); rw [coeff_zero_eq_constantCoeff_apply,coeff_zero_eq_constantCoeff_apply,constantCoeff_C]
 obtain ht:= m.neat he; rw [walk_c] at ht; rw [← m.service_lead (constantCoeff p) ]; exact Eq.trans (coeff_zero_eq_constantCoeff_apply _).symm ((ht _ le_rfl).trans (coeff_zero_eq_constantCoeff_apply _)) -- rw rhs only?

-- rising exact: not a piecewise approximation. Scalar compensation from field log.
lemma homes {i:ℕ}{v: Permit E}(h:Values v i) : Φ (X^i*C v )= X^i*C v:= by
 rw [_root_.map_mul, _root_.map_pow,walk_x, walk_c, service_value _ v h,mul_pow, mul_assoc ( X^i ), ← mul_assoc (carry m.p ^ i) (carry m.q ^ i), ← mul_pow (carry m.p) (carry m.q), ← map_mul (carry (E:=E)),m.old,map_one,one_pow,one_mul]
lemma any_rise [FiniteDimensional ℝ E](f:E→ℝ): Φ (Stack.rise f)=Stack.rise f:= by
 let V:= Stack.rise f; let v(n:ℕ):= coeff n V; let p(n:ℕ):= X^n*C (v n); let s n:=∑ i∈Finset.range (n+1),p i
 have he i: Φ (p i)= p i:= m.homes (fun x z => by unfold v V; rw [Stack.rise,coeff_mk]; exact jet_smul ..)
 have h n: Φ (s n)=s n:= by unfold s; simp_rw [map_sum,he]
 apply PowerSeries.ext; intro n; have hh: Through n V (s n):= by
    intro i hi; unfold s; rw [map_sum, Finset.sum_eq_single_of_mem i (Finset.mem_range.mpr (by omega)), show coeff i (p i)=_ from ?_]
    · unfold p; rw [ ← coin_m, coeff_monomial_same]
    intro j _ hj; unfold p; rw [ ← coin_m, coeff_monomial, if_neg (Ne.symm hj) ]
 rw [show coeff n (Φ (Stack.rise f))= _ from m.neat hh n le_rfl,h]; exact (hh n le_rfl).symm
end Move
end YM.FVA2.Recall
