import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.Algebra.MvPolynomial.Basic

/-!
# X-adic coefficient algebra of fixed-order kernels

X is the LOCAL rescaled coupling. `edit` permits a coefficient
substitution which itself outputs formal series (for Ward as well as
reset). No infinite sums involving polynomial variables or analytic convergence.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Blue
open PowerSeries Function
open scoped BigOperators
variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

/-- exclusive truncation: one X-adic ideal -/
def Equal (k:ℕ) (f g:PowerSeries R) : Prop := ∀ i<k, coeff i f=coeff i g
lemma Equal.refl (f:PowerSeries R)(k) : Equal k f f := fun _ _=>rfl
lemma Equal.symm {k} {f g:PowerSeries R} (h:Equal k f g) : Equal k g f := fun i hi=>(h i hi).symm
lemma Equal.trans {k} {f g h : PowerSeries R} (a:Equal k f g) (b:Equal k g h) : Equal k f h := fun i hi=>(a i hi).trans (b i hi)
lemma Equal.add {k} {f g f' g':PowerSeries R} (a:Equal k f f') (b:Equal k g g') : Equal k (f+g) (f'+g') := by intro i hi; simp_rw [map_add,a i hi,b i hi]
lemma Equal.mul {k} {f g f' g':PowerSeries R} (a:Equal k f f') (b:Equal k g g') : Equal k (f*g) (f'*g') := by
  intro i hi; rw [coeff_mul,coeff_mul]
  apply Finset.sum_congr rfl; intro j hj; obtain ⟨x,y⟩ := j
  have he : x+y=i := Finset.mem_antidiagonal.mp hj
  dsimp only; rw [a x (by omega),b y (by omega)]
lemma equal_iff {k} {f g:PowerSeries R} : Equal k f g ↔ X^k ∣ f-g := by simp [Equal,X_pow_dvd_iff,sub_eq_zero]
lemma filtered {ξ:PowerSeries R→+*PowerSeries S} (hx:constantCoeff (ξ X)=0) {f g:PowerSeries R} {k:ℕ} (h:Equal k f g) : Equal k (ξ f) (ξ g) := by
  apply equal_iff.mpr; rw [← map_sub]
  exact (pow_dvd_pow_of_dvd (X_dvd_iff.mpr hx) _).trans (by rw [← map_pow]; exact map_dvd ξ (equal_iff.mp h))
lemma shave (f:PowerSeries R) (k) : Equal k f (∑ i ∈ Finset.range k, C (coeff i f)*X^i) := by
  intro i hi; rw [map_sum,Finset.sum_eq_single_of_mem i (Finset.mem_range.mpr hi)];
  · simp
  intro j _ hj; simp [hj.symm]

private def editF (φ : R →+* PowerSeries S)(x:PowerSeries S)(f:PowerSeries R) :=
  PowerSeries.mk fun i => coeff i ((f.trunc (i+1)).eval₂ φ x)
private lemma edt (φ:R→+*PowerSeries S){x:PowerSeries S}(hx:constantCoeff x=0)(f:PowerSeries R){i k:ℕ}(hi:i<k) :
    coeff i (editF φ x f) = coeff i ((f.trunc k).eval₂ φ x) := by
  rw [editF, coeff_mk]; simp only [eval₂_trunc_eq_sum_range,map_sum]
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_of_lt hi)); intro j hj H
  apply X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd (X_dvd_iff.mpr hx) j |>.trans ?z) i ?l
  case z => exact dvd_mul_left ..
  case l => simp only [Finset.mem_range] at H; omega
private lemma edit_eq (φ:R→+*PowerSeries S){x:PowerSeries S}(hx:constantCoeff x=0) {f g:PowerSeries R}{k} (h:Equal k f g) : Equal k (editF φ x f) (editF φ x g) := by
  have hv : trunc k f=trunc k g := Polynomial.ext (by intro i; rw [coeff_trunc,coeff_trunc]; split_ifs with hh; exact h i hh; rfl)
  intro i hi; rw [edt φ hx f hi,edt φ hx g hi,hv]
private lemma edit_poly (φ:R→+*PowerSeries S){x:PowerSeries S}(hx:constantCoeff x=0)(p:Polynomial R) : editF φ x p=p.eval₂ φ x := by
  ext i; rw [edt φ hx ↑p (Nat.lt_succ_of_le (le_max_left i p.natDegree)),trunc_coe_eq_self (Nat.lt_succ_of_le (le_max_right ..))]
private lemma crop (f:PowerSeries R)(k:ℕ) : Equal k f ↑(trunc k f) := fun _ h => (coeff_coe_trunc_of_lt h).symm

/-- Simultaneous. The positive condition is required only on the
image of X; each image of a polynomial variable may have order zero. -/
def edit (φ:R→+*PowerSeries S){x:PowerSeries S}(hx:constantCoeff x=0) : PowerSeries R→+*PowerSeries S where
  toFun := editF φ x
  map_add' f g := by ext i; simp_rw [edt φ hx _ (Nat.lt_succ_self i), map_add,Polynomial.eval₂_add,map_add]; simp [editF]
  map_zero' := by ext i; simp [editF]
  map_one' := by simpa using edit_poly φ hx 1
  map_mul' f g := by
    ext i; let H:=trunc (i+1) f; let J:=trunc (i+1) g
    have hf : Equal (i+1) f ↑H := crop f (i+1); have hg : Equal (i+1) g ↑J := crop g (i+1)
    rw [edit_eq φ hx (hf.mul hg) i i.lt_succ_self, ((edit_eq φ hx hf).mul (edit_eq φ hx hg)) i i.lt_succ_self]
    rw [← Polynomial.coe_mul,edit_poly φ hx _,Polynomial.eval₂_mul,edit_poly φ hx _,edit_poly φ hx _]
lemma edit_coeff (φ:R→+*PowerSeries S){x:PowerSeries S}(hx:constantCoeff x=0)(f:PowerSeries R){i k : ℕ}(hi:i<k) :
    coeff i (edit φ hx f) = coeff i (∑ j∈Finset.range k,φ (coeff j f)*x^j) := by
  rw [← eval₂_trunc_eq_sum_range]; exact edt φ hx f hi
@[simp] lemma edit_C (φ:R→+*PowerSeries S){x:PowerSeries S}(hx:constantCoeff x=0)(r:R) : edit φ hx (C r)=φ r := by rw [← Polynomial.coe_C]; exact (edit_poly φ hx _).trans (Polynomial.eval₂_C ..)
@[simp] lemma edit_X (φ:R→+*PowerSeries S){x:PowerSeries S}(hx:constantCoeff x=0) : edit φ hx X=x := by rw [← Polynomial.coe_X]; exact (edit_poly φ hx _).trans (Polynomial.eval₂_X ..)
lemma serial_ext {χ ψ:PowerSeries R→+*PowerSeries S} (hx:constantCoeff (χ X)=0) (hc:∀ i,χ (C i)=ψ (C i)) (hX:χ X=ψ X) : χ=ψ := by
  have hv : constantCoeff (ψ X)=0:= by rw [← hX,hx]
  ext1 f; apply PowerSeries.ext; intro i
  rw [filtered hx (shave f _) i i.lt_succ_self,filtered hv (shave f _) i i.lt_succ_self]; simp_rw [map_sum,map_mul,map_pow,hc,hX]
lemma edited {χ:PowerSeries R→+*PowerSeries S} (hx:constantCoeff (χ X)=0) : χ= edit (χ.comp C) hx := serial_ext hx (fun i=> by rw [edit_C,RingHom.comp_apply]) (by rw [edit_X])

/-! X-adic exponential, its uniqueness and filtration law. -/

section Exp
variable [Algebra ℚ R]
def raiseE (f:PowerSeries R) : PowerSeries R := subst f (PowerSeries.exp R)
lemma raises {f:PowerSeries R}(h:constantCoeff f=0) : raiseE f = edit C h (PowerSeries.exp R) := by
  let M : PowerSeries R →+* PowerSeries R := (substAlgHom (HasSubst.of_constantCoeff_zero' h)).toRingHom
  have hx : M X=f := substAlgHom_X _
  have hc : M=edit C h := serial_ext (by rw [hx,h]) (fun i=> by rw [edit_C]; change substAlgHom _ _ = _; rw [coe_substAlgHom]; exact PowerSeries.subst_C i) (by rw [edit_X,hx])
  change _= _
  rw [←hc]; exact congr_fun (coe_substAlgHom (HasSubst.of_constantCoeff_zero' h)).symm _
lemma raise_one {f:PowerSeries R}(h:constantCoeff f=0) : constantCoeff (raiseE f)=1 := by
  rw [raises h,←coeff_zero_eq_constantCoeff_apply,edit_coeff _ h _ (Nat.lt_succ_self 0)]; simp
lemma raise_unit {f:PowerSeries R}(h:constantCoeff f=0) : IsUnit (raiseE f) := isUnit_iff_constantCoeff.mpr (by simp [raise_one h])
lemma raise_change {f:PowerSeries R}(h:constantCoeff f=0) : derivative R (raiseE f)=raiseE f*derivative R f := by unfold raiseE; rw [derivative_subst _ (HasSubst.of_constantCoeff_zero' h),derivative_exp]
lemma raise_map [Algebra ℚ S] (φ:PowerSeries R→+*PowerSeries S) (hx:constantCoeff (φ X)=0) {f:PowerSeries R} (hf:constantCoeff f=0) :
    φ (raiseE f)=raiseE (φ f) := by
  have hψ : constantCoeff (φ f)=0 := X_dvd_iff.mp ((X_dvd_iff.mpr hx).trans (map_dvd φ (X_dvd_iff.mpr hf)))
  let Y : PowerSeries ℚ := PowerSeries.exp ℚ
  have eqA : PowerSeries.exp R= PowerSeries.map (algebraMap ℚ R) Y := (PowerSeries.map_exp _).symm
  have eqB : PowerSeries.exp S= PowerSeries.map (algebraMap ℚ S) Y := (PowerSeries.map_exp _).symm
  rw [raises hf, raises hψ,eqA, eqB]
  let J:= φ.comp ((edit C hf).comp (PowerSeries.map (algebraMap ℚ R)))
  let K:= (edit C hψ).comp (PowerSeries.map (algebraMap ℚ S))
  have hX : J X = K X := by simp [J,K]
  have hy : J=K := serial_ext (by rw [hX]; simpa [K]) (fun a=> by
      change φ _ = _; simp only [K,RingHom.comp_apply,map_C,edit_C]
      simp_rw [RingHom.map_rat_algebraMap C,RingHom.map_rat_algebraMap φ]) hX
  exact DFunLike.congr_fun hy _
variable [IsAddTorsionFree R]
omit [Algebra ℚ R] in
lemma raise_unique (f : PowerSeries R) {u v:PowerSeries R} (hu:derivative R u=u*f) (hv:derivative R v=v*f) (hc:constantCoeff u=constantCoeff v) : u=v := by
  ext n; induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa only [coeff_zero_eq_constantCoeff_apply]
    | succ n =>
      have eq := (show Equal _ u v from ih).mul (Equal.refl f (n+1)) n (n.lt_succ_self)
      rw [←hu,←hv,coeff_derivative,coeff_derivative,mul_comm _ ((n:R)+1),mul_comm _ ((n:R)+1),← Nat.cast_succ,← nsmul_eq_mul,← nsmul_eq_mul] at eq
      exact (smul_right_inj n.succ_ne_zero).mp eq
lemma raise_add {f g:PowerSeries R} (hf:constantCoeff f=0)(hg:constantCoeff g=0) : raiseE (f+g)=raiseE f * raiseE g := by
  have hv : constantCoeff (f+g)=0 := by simp [hf,hg];
  apply raise_unique _ (raise_change hv)
  · rw [Derivation.leibniz,raise_change hf,raise_change hg,map_add]; simp only [smul_eq_mul]; ring
  rw [map_mul,raise_one hf,raise_one hg,raise_one hv,one_mul]
lemma raise_inj {f g:PowerSeries R} (hf:constantCoeff f=0)(hg:constantCoeff g=0)(he:raiseE f=raiseE g) : f=g := by
  have hF := raise_change hf; rw [he,raise_change hg] at hF
  exact derivative.ext ((raise_unit hg).mul_right_inj.mp hF.symm) (hf.trans hg.symm)
-- use mathlib's logOf
lemma raising_log {f:PowerSeries R}(hf:constantCoeff f=1) : raiseE (logOf f)=f := by
  have hv : constantCoeff (logOf f)=0:= constantCoeff_logOf hf
  apply raise_unique _ (raise_change hv) _ (by rw [raise_one hv,hf])
  have hu : constantCoeff (f-1)=0:= by rw [map_sub,hf,map_one,sub_self];
  have h := HasSubst.of_constantCoeff_zero' hu
  have he : (1+X)*(derivative R (log R))=1 := by
    ext n; rw [deriv_log,add_mul,one_mul,map_add]; cases n
    · simp
    · simp [_root_.pow_succ]
  have hx : f*(derivative R (log R)).subst (f-1)=1 := by
    have H := congr_arg (fun u=>PowerSeries.subst (f-1) u) he
    simp only [subst_mul h,subst_add h,subst_X h,← coe_substAlgHom h,map_one] at H ⊢
    convert H using 2
    ring
  rw [logOf_eq,derivative_subst _ h,map_sub,Derivation.map_one_eq_zero,sub_zero,← mul_assoc,hx,one_mul]
end Exp

end YM.WilsonCoeffUV.Blue
