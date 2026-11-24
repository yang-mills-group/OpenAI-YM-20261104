import YangMills.WilsonProof.NativeSupport.Commissioned122.Scoped.YM.GradedFar.Toward.SeparateLegs
/-!
# A second spend of F.O in the application

Also pay exactly the omission price (line 1692): the omitted powers after applying
the Far conversion before evaluating the cropped raw formal moments. Works both
for unconverted pullbacks of predictions and for the crops with the entire Scale
leg maps (section E dual measurement). Still an independent formal-book estimate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar
open Function Filter Set Scale O.Score O.Enh O.Canon PowerSeries XSpace XSpace.Normalize Dframe
open private guardedAppend column_at from YangMills.WilsonProof.NativeSupport.Commissioned122.Scoped.YM.GradedFar.Expansion
open scoped Topology Classical BigOperators

variable {G : Gauge} {V : Arenas G} {ψ : ℝ → PowerSeries ℂ} {B : ℝ → Frames G}
    (phys : Physical V ψ B) (law : Law V ψ B)
    {n m h k p q H : ℕ} {d : Fin n → ℕ} {e : Fin m → ℕ}
    {K : Set (Points n)} {S : Set (Points m)} (kc : IsCompact K) (hk : K⊆conf n)
    (sc : IsCompact S) (hs : S⊆Outside m)
    (hd : Covered d H) (he : Covered e H)
    (u : Scan G n) (v : Scan G m) (oldU : ∀ i, heft (u i) ≤ d i) (oldV : ∀ i, heft (v i) ≤ e i)
include phys

include law in
lemma expand_term (z : Points (n+m)) (η : ℝ) (s : Days m) :
    orderedTerm V B η z hd he s (fun i => cap (u i) (oldU i)) (fun i => cap (v i) (oldV i)) =
      ∑ p : LivesP v, (O.Score.fee η (totalG v) * ∏ j : Fin m, coeff (s (some j))
        (cue (seats (B η)) (v j) (decode v p j))) * coeff (s none) (install V _ z (Fin.append u (decode v p))) := by
  let U : Guarded u H := fun i => (oldU i).trans (hd i)
  let W (p : LivesP v) : Guarded (decode v p) H := fun i => (oldV i).trans (he i)
  let Z := curried (extAt V z H (s none)) (tape u U)
  have entry (p : LivesP v) : coeff (s none) (install V (n+m) z (Fin.append u (decode v p))) = Z (tape _ (W p)) := by
    rw [coeff_install_eq V z phys.dimensions _ (guardedAppend u (decode v p) U (W p)), tape_append]
    exact (curried_apply ..).symm
  rw [orderedTerm, mix_apply, ← curried_apply]; simp_rw [column_at law v he oldV]
  rw [MultilinearMap.map_sum]; refine Finset.sum_congr rfl fun p _ => ?_
  rw [MultilinearMap.map_smul_univ]; simp only [Finset.prod_mul_distrib, priced, smul_eq_mul, entry]; rfl

lemma unconverted_label (z : Points (n+m)) : unconverted V z hd he (fun i => cap (u i) (oldU i)) (fun i => cap (v i) (oldV i)) =
    install V _ z (Fin.append u v) := by
  ext k
  let U : Guarded u H := fun i => (oldU i).trans (hd i)
  let W : Guarded v H := fun i => (oldV i).trans (he i)
  rw [unconverted_coeff, mix_apply, coeff_install_eq V z phys.dimensions _ (guardedAppend u v U W), tape_append u v U W]; rfl

abbrev log_layout (K : Set (Points n)) (S : Set (Points m)) (i : Profiles K S) (t : ℝ) := forest i.1.val (squeeze (-t) i.2.val)
omit phys in
lemma log_fee {X : Type} (j : ℕ) : Rain (-(j:ℝ)) (fun (_:X) t => O.Score.fee (-t) j) := by
  have h : ∀ t:ℝ, O.Score.fee (-t) j = O.Score.fee t (-(j:ℝ)) := by intro t; unfold O.Score.fee; simp
  simp_rw [h]; exact Rain.all_fee

omit phys in
lemma Rain_prod {X D : Type} (t : Finset D) (f : D → X → ℝ → ℂ) (h : ∀ i∈t, Rain 0 (f i)) :
    Rain 0 (fun i k => ∏ j∈t, f j i k) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact Rain.fixed _
  | insert i s h₀ ih =>
    simp only [Finset.prod_insert h₀]; exact Rain.cover (h i (Finset.mem_insert_self ..))
      (ih (fun j hj => h _ (Finset.mem_insert_of_mem hj)))

include kc hk sc hs
include law in
lemma term_rain (u : Words G d) (v : Words G e) (s : Days m) :
    Rain 0 (fun i : Profiles K S => fun t => orderedTerm V B (-t) (log_layout K S i t) hd he s (basisFields u) (basisFields v)) := by
  let D := ℂ
  let W := labeling v
  have h i t := expand_term phys law hd he (labeling u) (labeling v)
    (fun i => size_le (u i)) (fun i => size_le (v i)) (log_layout K S i t) (-t) s
  change Rain 0 (fun (i : Profiles K S) (t:ℝ) => orderedTerm V B (-t) (log_layout K S i t) hd he s
    (fun j => cap (labeling u j) (size_le (u j))) (fun j => cap (labeling v j) (size_le (v j))))
  simp_rw [h]; apply Rain.sum; intro p _
  apply Rain.size (a:=-(totalG W:ℝ)+(totalG W:ℝ)) _ (by simp)
  have H j := Rain.rhythm (I:=Profiles K S) (polynomial_cost law (labeling v j) (p j) (s (some j)))
  exact Rain.mul (Rain.wig (log_fee _) (Rain_prod _ _ (fun j _ => H j)))
    (Full_basis phys kc hk sc hs (labeling u) (decode _ p) 0 (s none) (s none) (Nat.lt_succ_self _))

lemma Full_coin_rain (u : Words G d) (v : Words G e) (k : ℕ) :
    Rain (totalG (labeling v) : ℝ) (fun (i : Profiles K S) t =>
      mix V (log_layout K S i t) k hd he (fun _ => 1) (basisFields u) (basisFields v)) := by
  have h t i := unconverted_label phys hd he (labeling u) (labeling v)
    (fun i => size_le (u i)) (fun i => size_le (v i)) (log_layout K S i t)
  have h : ∀ (i:Profiles K S) (t:ℝ), unconverted V (log_layout K S i t) hd he (basisFields u) (basisFields v) =
      install V _ (log_layout K S i t) (Fin.append (labeling u) (labeling v)) := fun i t => h t i
  simp_rw [← unconverted_coeff,h]; exact Full_basis phys kc hk sc hs (labeling u) (labeling v) 0 k k (Nat.lt_succ_self _)

-- Multilinearity helpers.
variable {I : Type} (x : I → Points n) (hx : ∀ i, x i∈K) (y : I → Points m) (hy : ∀ i, y i∈S)
    (u : I → Appointed122Fields G d) (v : I → Appointed122Fields G e) {R L : ℝ} (hu : ∀ i, FieldBudget (u i) R) (hv : ∀ i, FieldBudget (v i) L)
    (p q : ℕ) (t : I → ℂ) (ht : ∀ i, ‖t i‖ ≤ 1)

omit phys kc hk sc hs in
private lemma rain_factor {F : I → ℝ → Form G d (Form G e ℂ)} {R L a : ℝ}
    (hu : ∀ i, FieldBudget (u i) R) (hv : ∀ i, FieldBudget (v i) L)
    (h : ∀ i j, Rain a (fun w z => F w z (basisFields i) (basisFields j))) :
    Rain a (fun w z => F w z (u w) (v w)) := by
  simp_rw [decompose_form (F ..) (u _), _root_.sum_apply, _root_.smul_apply,
    decompose_form ((F _ _) (basisFields _)) (v _), smul_eq_mul]
  apply Rain.sum; intro i _; refine Rain.cover (Rain.cash ⟨R^n, fun w => multiplier_budget (u w) (hu w) i⟩) ?_
  apply Rain.sum; intro j _; exact Rain.cover (Rain.cash ⟨L^m, fun w => multiplier_budget (v w) (hv w) j⟩)
    (h i j)

include hx hy hu hv ht
lemma legBillRawRain122 : Rain 0 (fun i z => filedCrop122 p (t i) (unconverted V
    (forest (x i) (squeeze (-z) (y i))) hd he (u i) (v i))) := by
  simp_rw [filedCropEq122, unconverted_coeff]; apply Rain.sum; intro k _
  refine Rain.wig (rain_factor u v hu hv ?_) (powers_price t ht k); intro p q
  exact Rain.size ((Full_coin_rain phys kc hk sc hs hd he p q k).pull
    (fun i => (⟨x i,hx i⟩,⟨y i,hy i⟩))) (by positivity)

include law in
lemma omit_rain : Rain 0 (fun i z => preBill V B (-z) (forest (x i) (squeeze (-z) (y i))) hd he p q (t i) (u i) (v i)) := by
  simp_rw [preBill, _root_.sum_apply, _root_.smul_apply, smul_eq_mul]
  apply Rain.sum; intro i _
  refine Rain.cover (powers_price t ht _) (rain_factor u v hu hv ?_); intro p q
  exact (term_rain phys law kc hk sc hs hd he p q _).pull fun i => (⟨x i,hx i⟩,⟨y i,hy i⟩)

omit hx hy hu hv ht
include law in
theorem omit_price (hq : p ≤ q) (R L : ℝ) : ∃ C : ℝ, 0 < C ∧ ∃ a : ℕ, ∀ᶠ T in (atTop : Filter ℝ),
    ∀ x ∈ K, ∀ y ∈ S, ∀ u : Appointed122Fields G d, ∀ v : Appointed122Fields G e, FieldBudget u R → FieldBudget v L →
    ∀ z : ℂ, ‖z‖ ≤ 1 → ‖filedCrop122 p z (unconverted V (forest x (T • y)) hd he u (applied B (-Real.log T) v q z)) -
        jointY V B hd he u v p z T x y‖ ≤ C*(1+Real.log T)^a * ‖z‖^(p+1) := by
  let I := Profiles K S × ({u : Appointed122Fields G d // FieldBudget u R} × {v : Appointed122Fields G e // FieldBudget v L}) × UnitDisk
  have price := omit_rain phys law kc hk sc hs hd he (I:=I)
    (fun i => i.1.1.val) (fun i => i.1.1.property) (fun i => i.1.2.val) (fun i => i.1.2.property)
    (fun i => i.2.1.1.val) (fun i => i.2.1.2.val) (fun i => i.2.1.1.property) (fun i => i.2.1.2.property)
    p q (fun i => i.2.2.val) (fun i => i.2.2.property)
  obtain ⟨C,hC,b,E⟩ := toSpatial 0 (by rw [Nat.cast_zero]; exact price)
  refine ⟨C,hC,b,?_⟩; filter_upwards [E,eventually_gt_atTop (0:ℝ)] with T w ht x hx y hy u v hu hv z hz
  rw [recropping V B (-Real.log T) _ hd he u v p q z hq, jointY, add_sub_cancel_left,
    ← squeeze_log ht, norm_mul, norm_pow]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  simpa only [pow_zero, inv_one,mul_one] using w (((⟨x,hx⟩,⟨y,hy⟩), (⟨u,hu⟩,⟨v,hv⟩), ⟨z,hz⟩) : I)

lemma raw_price (R L : ℝ) : ∃ C : ℝ, 0 < C ∧ ∃ a : ℕ, ∀ᶠ T in (atTop : Filter ℝ),
    ∀ x ∈ K, ∀ y ∈ S, ∀ u : Appointed122Fields G d, ∀ v : Appointed122Fields G e, FieldBudget u R → FieldBudget v L →
    ∀ z : ℂ, ‖z‖ ≤ 1 → ‖filedCrop122 p z (unconverted V (forest x (T • y)) hd he u v)‖ ≤ C*(1+Real.log T)^a := by
  let I := Profiles K S × ({u : Appointed122Fields G d // FieldBudget u R} × {v : Appointed122Fields G e // FieldBudget v L}) × UnitDisk
  have price := legBillRawRain122 phys kc hk sc hs hd he (I:=I)
    (fun i => i.1.1.val) (fun i => i.1.1.property) (fun i => i.1.2.val) (fun i => i.1.2.property)
    (fun i => i.2.1.1.val) (fun i => i.2.1.2.val) (fun i => i.2.1.1.property) (fun i => i.2.1.2.property)
    p (fun i => i.2.2.val) (fun i => i.2.2.property)
  obtain ⟨C,hC,b,E⟩ := toSpatial 0 (by rw [Nat.cast_zero]; exact price)
  refine ⟨C,hC,b,?_⟩; filter_upwards [E,eventually_gt_atTop (0:ℝ)] with T w ht x hx y hy u v hu hv z hz
  rw [← squeeze_log ht]
  simpa only [pow_zero, inv_one,mul_one] using w (((⟨x,hx⟩,⟨y,hy⟩), (⟨u,hu⟩,⟨v,hv⟩), ⟨z,hz⟩) : I)
end YM.FVA2.GradedFar
