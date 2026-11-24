import YangMills.WilsonProof.NativeSupport.Commissioned122.Scoped.YM.GradedFar.Toward.LegBill
/-!
# After applying the actual Far scale, still have room for that remainder

Here estimate the cost of plugging the *actual* scale ratios into the
independently predicted answers **at those same positions**, having paid
G.1. This is a use of the same (M.2) construction and charge. Purchase
actual operands/remaining budgets separately from this part.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar
open Filter Function Set Scale O.Score O.Enh O.Canon PowerSeries XSpace XSpace.Normalize Dframe
open scoped Topology Classical BigOperators

variable {G : Gauge} {V : Arenas G} {ψ : ℝ → PowerSeries ℂ} {B : ℝ → Frames G}
    (phys : Physical V ψ B) (law : Law V ψ B)
    {n m h k p q H : ℕ} {d : Fin n → ℕ} {e : Fin m → ℕ}
    {K : Set (Points n)} {S : Set (Points m)} (kc : IsCompact K) (hk : K⊆conf n)
    (sc : IsCompact S) (hs : S⊆Outside m) (hd : Covered d H) (he : Covered e H)

section
variable (V B) (u : Appointed122Fields G d) (v : Appointed122Fields G e) (p : ℕ) (z : Points (n+m)) (η : ℝ) (f : ℂ)

/-- Useful packaging; copies no data. -/
def bareModel (V : Arenas G) : Form G d (Form G e ℂ) := ∑ i∈Finset.range (p+1), f^i • mix V z i hd he (fun _ => 1)
lemma bareModel_apply : bareModel hd he p z f V u v = filedCrop122 p f (unconverted V z hd he u v) := by
  unfold bareModel; rw [filedCropEq122]; simp_rw [_root_.sum_apply,_root_.smul_apply,smul_eq_mul,unconverted_coeff];
  exact Finset.sum_congr rfl fun i _ => mul_comm ..

def fittedModel (V : Arenas G) (B : ℝ → Frames G) (η : ℝ) : Form G d (Form G e ℂ) :=
  ∑ i∈Finset.range (p+1), f^i • ordered V (fun i => transfer B η (e i)) z hd he i
lemma fitted_apply : fittedModel hd he p z f V B η u v = filedCrop122 p f (series V B η z hd he u v) := by
  unfold fittedModel; rw [filedCropEq122]; simp_rw [_root_.sum_apply,_root_.smul_apply,smul_eq_mul,series_coeff];
  exact Finset.sum_congr rfl fun i _ => mul_comm ..
end

section move
variable {F : Form G e ℂ} {T r δ : ℝ} (C : Fin m → ℝ)

def slotNorm {G : Gauge} {d : ℕ} (u : Sec G d) := ‖account G d u‖
def localLegs (C : Fin m → ℝ) (v : Appointed122Fields G e) := ∀ i, slotNorm (v i) ≤ C i

lemma fees (f : Form G e ℂ) {A : ℝ} (h : ∀ v : Appointed122Fields G e, FieldBudget v 1 → ‖f v‖ ≤ A)
    (x : Appointed122Fields G e) (C : Fin m → ℝ) (hc : ∀ i, 0 < C i) (hx : localLegs C x) :
    ‖f x‖ ≤ (∏ i, C i)*A := by
  let a (i : Fin m) : ℂ := C i; let y (i : Fin m) := (a i)⁻¹ • x i
  have ha i : ‖a i‖ = C i := by simp [a,Real.norm_eq_abs,abs_of_pos (hc i)]
  have hz i : a i ≠ 0 := Complex.ofReal_ne_zero.mpr (hc i).ne'
  have hw : x = (fun i => a i • y i) := funext (fun i => by unfold y; rw [smul_smul,mul_inv_cancel₀ (hz i),one_smul])
  have hv : FieldBudget y 1 := (fieldBudget_iff y zero_le_one).mpr (fun i => by
    rw [show y i = (a i)⁻¹ • x i from rfl,map_smul,norm_smul,norm_inv,ha,mul_comm, ← div_eq_mul_inv]
    exact (div_le_one (hc i)).mpr (hx i))
  rw [hw, MultilinearMap.map_smul_univ, norm_smul, norm_prod]; simp_rw [ha]
  exact mul_le_mul_of_nonneg_left (h y hv) (Finset.prod_nonneg (fun i _ => (hc i).le))

/-- Pay for differences of legs with a common **relative** error budget δ. -/
lemma replaceFields (f : Form G e ℂ) {A : ℝ} (h : ∀ v : Appointed122Fields G e, FieldBudget v 1 → ‖f v‖ ≤ A)
    (x y : Appointed122Fields G e) (C : Fin m → ℝ) (hc : ∀ i, 0 < C i) (hx : localLegs C x)
    (hy : localLegs C y) (hδ : 0 < δ) (hs : localLegs (fun i => δ*C i) (x-y)) :
    ‖f x - f y‖ ≤ (m:ℝ)*(δ*(∏ i, C i)*A) := by
  let g (i j : Fin m) := if j < i then x j else if i=j then x j-y j else y j
  have eq : f x-f y = ∑ j : Fin m, f (g j) := by
    simpa only [Finset.piecewise_univ, Finset.mem_univ,true_imp_iff,g] using f.map_sub_map_piecewise x y Finset.univ
  have H (i : Fin m) : ‖f (g i)‖ ≤ δ * (∏ i, C i)*A := by
    let C' (j : Fin m) := (if i=j then δ else 1)*C j
    have heq : (∏ j, C' j) = δ * ∏ j, C j := by unfold C'; rw [Finset.prod_mul_distrib]; simp
    rw [← heq]; refine fees f h (g i) C' (fun j => by
      unfold C'; split <;> exact mul_pos (by positivity) (hc j)) ?_
    intro j; unfold g C'; split
    · rename_i hi; rw [if_neg hi.ne',one_mul]; exact hx j
    split_ifs <;> first | exact hs j | exact (hy _).trans_eq (one_mul ..).symm
  rw [eq]; exact (norm_sum_le ..).trans ((Finset.sum_le_sum (fun i _ => H i)).trans_eq (by simp [nsmul_eq_mul]))

/-- Convenient standard budget when estimating calls over the label balls. Same
norm used in the physical hypotheses. -/
def actsSize {k : ℕ} (F : FieldEnd G k) (b : ℝ) :=
  ∀ v : Sec G k, slotNorm (F v) ≤ b*slotNorm v
lemma actB (v : Appointed122Fields G e) {R : ℝ} (nonneg : 0 ≤ R) (legs : FieldBudget v R) (u : ∀ i, FieldEnd G (e i))
    (C : Fin m → ℝ) (hc : ∀ i, 0 ≤ C i) (h : ∀ i, actsSize (u i) (C i)) : localLegs (fun i => C i * R) (preapply u v) :=
  fun i => (h i (v i)).trans (mul_le_mul_of_nonneg_left ((fieldBudget_iff v nonneg).mp legs i) (hc i))
end move

variable (p q : ℕ) {T U W c g L D E : ℝ} {x : Points n} {y : Points m} (u : Appointed122Fields G d) (v : Appointed122Fields G e) (z : ℂ)

/-- One numerical experiment (family will be assembled later). Assume exactly
inputs for comparing all-H_r phase reading on such y, T to the independent formal
kernels on those same Sec inputs, and for the costs of changing every label on it.

* `eval`: first compare all-H_r to the cropped *unconverted* predictor (with its
shape dependence already paid through-p).
* `fore`: actual Far labels in r coframe with growing-T cost.
* `diff`: precision from using p' ≥ p crop of K chosen by G.1. Even `D*g^(p+1)` suffices,
here using uniform along all labels -- the stronger precision in §M works as well.

Constants simplified to common A. Also pass the previously proved log price on raw and
omitted power price; they hold eventually with a large enough constant and exponent. -/
lemma first_cost (T g A : ℝ) (a : ℕ) (hT : 1 ≤ T) (hA : 1 ≤ A) (hg : 0 < g) (bg : g ≤ 1)
    (Y : Form G e ℂ) (F : ∀ i, FieldEnd G (e i)) (hv : FieldBudget v 1)
    (fore : ∀ i, actsSize (F i) (A*T^(e i)))
    (diff : ∀ i, actsSize (F i-croppedTransfer B (-Real.log T) q z (e i)) (A*g^(p+1)))
    (raw : ∀ w : Appointed122Fields G e, FieldBudget w 1 →
      ‖filedCrop122 p z (unconverted V (forest x (T • y)) hd he u w)‖ ≤ A*(1+Real.log T)^a)
    (eval : ∀ w : Appointed122Fields G e, FieldBudget w 1 →
      ‖Y w - filedCrop122 p z (unconverted V (forest x (T • y)) hd he u w)‖ ≤ A*g^(p+1)*(1+Real.log T)^a)
    (payment : ‖filedCrop122 p z (unconverted V (forest x (T • y)) hd he u (applied B (-Real.log T) v q z)) -
        jointY V B hd he u v p z T x y‖ ≤ A*g^(p+1)*(1+Real.log T)^a) :
    ‖Y (preapply F v) - jointY V B hd he u v p z T x y‖ ≤
      ( (m+1)*(2*A)^m+1 )*A * T^(∑ i, e i) * g^(p+1) * (1+Real.log T)^a := by
  let Z := bareModel hd he p (forest x (T • y)) z V u
  let w' := preapply F v; let K (i : Fin m) := croppedTransfer B (-Real.log T) q z (e i)
  let k' := preapply K v
  let d (i : Fin m) := 2*A*T^(e i)
  let δ := g^(p+1); let P := (1+Real.log T)^a
  have Ap := zero_lt_one.trans_le hA; have Tp := zero_lt_one.trans_le hT
  have hl := Real.log_nonneg hT
  have dp (i : Fin m) : 0 < d i := by dsimp [d]; positivity
  have L i : slotNorm (w' i) ≤ A*T^(e i) := by
    exact (actB v zero_le_one hv F _ (fun i => by positivity) fore i).trans_eq (mul_one _)
  have W : localLegs d w' := fun i => (L i).trans (by dsimp only [d]; gcongr; linarith)
  have tδ : δ ≤ 1 := pow_le_one₀ hg.le bg
  have B' i : slotNorm ((w'-k') i) ≤ A*δ := (actB v zero_le_one hv
    (fun i => F i-K i) _ (fun i => by positivity) diff i).trans_eq (mul_one _)
  have R : localLegs d k' := fun i => by
    have Hp : A ≤ A*T^(e i) := le_mul_of_one_le_right Ap.le (one_le_pow₀ hT)
    have Hp' : A*δ ≤ A := mul_le_of_le_one_right Ap.le tδ
    have a := B' i
    have b := L i
    change ‖account G (e i) (w' i-k' i)‖ ≤ _ at a
    rw [map_sub, norm_sub_rev] at a
    unfold slotNorm at *; unfold d
    have s := norm_sub_norm_le (account G (e i) (k' i)) (account G (e i) (w' i))
    linarith only [Hp,Hp',s,a,b]
  have hf : localLegs (fun i => δ*d i) (w'-k') := fun i =>
    (B' i).trans (by rw [mul_comm A]; apply mul_le_mul_of_nonneg_left _ (pow_nonneg hg.le _);
                     exact (le_mul_of_one_le_right Ap.le (one_le_pow₀ (n:=e i) hT)).trans (by dsimp [d]; gcongr; linarith))
  have rp : ∀ w, FieldBudget w 1 → ‖Z w‖ ≤ A*P := by intro w hw; dsimp only [Z]; rw [bareModel_apply]; exact raw _ hw
  have ep : ∀ w, FieldBudget w 1 → ‖(Y-Z) w‖ ≤ A*δ*P := by
    intro w hw; change ‖Y w-bareModel _ _ _ _ _ _ _ w‖ ≤ _; rw [bareModel_apply]; exact eval w hw
  have a := fees (Y-Z) ep w' d dp W
  have b := replaceFields Z rp w' k' d dp W R (pow_pos hg (p+1)) hf
  have result : (∏ i, d i) = (2*A)^m*T^(∑ i,e i) := by
    unfold d; rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]; simp
  rw [result] at a b
  let Y' := jointY V B hd he u v p z T x y
  have c : ‖Z k'-Y'‖ ≤ A*δ*P := by dsimp only [Z]; rw [bareModel_apply]; exact payment
  change ‖Y (preapply F v)-Y'‖ ≤ _
  rw [show Y (preapply F v)-Y'= (Y-Z) w'+((Z w'-Z k')+(Z k'-Y')) by
    change Y w'-Y'=Y w'-Z w'+((Z w'-Z k')+(Z k'-Y')); abel]
  apply le_trans (norm_add_le ..)
  apply le_trans (add_le_add a ((norm_add_le ..).trans (add_le_add b c)))
  calc _ ≤ ((2*A)^m*T^(∑ i,e i))*(A*δ*P)+(m*(δ*((2*A)^m*T^(∑ i,e i))*(A*P))+ A*δ*P*T^(∑ i,e i)) := by
          apply add_le_add le_rfl (add_le_add le_rfl ?_); exact le_mul_of_one_le_right (by unfold P δ; positivity) (one_le_pow₀ hT)
       _ = _ := by dsimp only [P,δ]; ring
end YM.FVA2.GradedFar
