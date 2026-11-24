import YangMills.WilsonProof.NativeSupport.Commissioned122.Scoped.YM.GradedFar.Rows
import YM.FVA2.O.Read.Zone

/-!
# Bridge: LensT is exactly the field-inserted formal row

Including the running matrix on **every** Far field. There is no projection
onto low grades in these identities. `series` uses the literal Scale machinery
at each field's cap, before cropping, not estimates specialized to basis legs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar
open Function Scale O O.Score O.Enh O.Read O.Project PowerSeries
open XSpace XSpace.Normalize Dframe MS.Book.Program
open scoped Classical BigOperators

variable {G : Gauge} {H l k p h n m : ℕ} {V : Arenas G} {ψ : ℝ → PowerSeries ℂ} {B : ℝ → Frames G}
    (law : Law V ψ B)

include law
/-- Any order of any weight column: a common scale power times a linear combination of
precisely *that* grade, using the stock running matrix. (`cap_map` with Civil is where
Native, coherence on all horizons, etc. from the homogeneous law enter.) -/
lemma column (q : Q G) (hq : heft q ≤ l) (j : ℕ) (η : ℝ) :
    coeff j (transfer B η l) (cap q hq) =
      ∑ i : Grade G (heft q), (Extent.token η (heft q) * coeff j (cue (seats (B η)) q (own i))) •
        cap (own i) (d:=l) hq := by
  rw [transfer_apply, cap_map (slot law η), map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [_root_.map_smul, cap, Level.exact₀, smul_smul, mul_comm]; rfl

omit law in
lemma token_log (T : ℝ) (hT : 0 < T) : Extent.token (-Real.log T) h = (T : ℂ)^h := by
  simp only [Extent.token, neg_neg, Real.exp_log hT]

/-- Its remaining entries are *polynomials* in the log scale, through any desired order. -/
lemma polynomial_cost (q : Q G) (w : Grade G (heft q)) (k : ℕ) :
    Rhythm (fun t => coeff k (cue (seats (B (-t))) q (own w))) := by
  simp_rw [report]; exact Uniform.flips (rhythm_v law) _ _ _ k

variable (z : Points (n+m)) (u : Scan G n) (v : Scan G m)
    {d : Fin n → ℕ} {e : Fin m → ℕ}
    (hd : Covered d H) (he : Covered e H) (hu : ∀ i, heft (u i) ≤ d i)
    (hv : ∀ i, heft (v i) ≤ e i)

omit law
private lemma guardedAppend (U : Guarded u H) (W : Guarded v H) : Guarded (Fin.append u v) H := by
  intro i; induction i using Fin.addCases <;> simp only [Fin.append_left, Fin.append_right] <;> solve
  | exact U _
  | exact W _

lemma tape_append (U : Guarded u H) (W : Guarded v H) :
    tape (Fin.append u v) (guardedAppend u v U W) = Fin.append (tape u U) (tape v W) := by
  funext i; induction i using Fin.addCases <;> simp [tape]

include law
private lemma column_at (α : ℝ) (s : Days m) (j : Fin m) :
    up (he j) (coeff (s (some j)) (transfer B α (e j)) (cap (v j) (hv j))) =
      ∑ w : Grade G (heft (v j)), (Extent.token α (heft (v j))*
        coeff (s (some j)) (cue (seats (B α)) (v j) (own w))) • cap (own w) (d:=H) ((hv j).trans (he j)) := by
  rw [column law, map_sum]; simp only [_root_.map_smul]; rfl

/-- Use once at each homogeneous tuple (FieldBudget will be handled separately).
Even off configurations this equality holds, by standard extension by zero. -/
theorem expand (regular : Regular V) (η : ℝ) :
    series V B η z hd he (fun j => cap (u j) (hu j)) (fun i => cap (v i) (hv i)) =
      Acres η (totalG v) * concert (seats (B η)) v (fun w => install V _ z (Fin.append u w)) := by
  ext k
  let U : Guarded u H := fun i => (hu i).trans (hd i)
  let W (p : LivesP v) : Guarded (decode v p) H := fun i => (hv i).trans (he i)
  let Z (i : Days m) := curried (extAt V z H (i none)) (tape u U)
  have entry (i : Days m) (p : LivesP v) : coeff (i none)
      (install V (n+m) z (Fin.append u (decode v p))) = Z i (tape _ (W p)) := by
    rw [coeff_install_eq V z regular _ (guardedAppend u (decode v p) U (W p)), tape_append];
    exact (curried_apply ..).symm
  rw [series_coeff, ordered_apply]; simp_rw [← curried_apply, column_at law v he hv]
  unfold Acres concert play; rw [coeff_C_mul, map_sum]; simp_rw [Constants.admits, entry]
  rw [Finset.sum_comm, Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
  rw [MultilinearMap.map_sum, Finset.mul_sum]; refine Finset.sum_congr rfl fun p _ => ?_
  rw [MultilinearMap.map_smul_univ]; simp only [Finset.prod_mul_distrib, priced, smul_eq_mul];
  rw [mul_assoc]; rfl

lemma expand_basis (regular : Regular V) (η : ℝ) (u : Words G d) (v : Words G e) :
    series V B η z hd he (basisFields u) (basisFields v) =
      Acres η (totalG (labeling v)) * concert (seats (B η)) (labeling v)
        (fun w => install V _ z (Fin.append (labeling u) w)) :=
  expand law z (labeling u) (labeling v) hd he (fun i => size_le (u i)) (fun i => size_le (v i)) regular η

/-- `ShowT` **is** the homogeneous full series row. -/
lemma expand_show (regular : Regular V) (x : Points n) (y : Points m)
    (t : ℝ) (u : Words G d) (v : Words G e) :
    series V B (-t) (forest x (squeeze (-t) y)) hd he (basisFields u) (basisFields v) =
      ShowT B (install V) t x (labeling u) y (labeling v) :=
  expand_basis law _ hd he regular _ u v

/-- And `LongT` **is** every homogeneous response. -/
lemma expand_long (regular : Regular V) (lh : h ≤ H) (y : Points m)
    (t : ℝ) (q : Toon G h) (v : Words G e) :
    rowsResponse122 V B (-t) (outgoing (squeeze (-t) y)) h lh he (basisFields v) (theory q) =
      LongT B (install V) t (flash q) y (labeling v) :=
  expand_show law (d:=fun _ : Fin 1 => h) (fun _ => lh) he regular (0 : Points 1) y t
    (fun _ => q) v
end YM.FVA2.GradedFar
