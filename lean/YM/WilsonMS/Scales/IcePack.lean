import YM.WilsonMS.Scales.Stance
/-!
# Invert about the calibrated point

All formal coupling inverses here are compositional (`c(0)=0`). Fast along
prepared array order-by-order on a common schedule.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.Ice
open Function Set Filter MeasureTheory Real Finset Metric
open XSpace XSpace.Normalize XSpace.Expense XSpace.Cirrus XSpace.TestBudget XSpace.Structure1 Lattice
open Maxwell Maxwell.Free Maxwell.Wick VisitH
open MS MS.Menus MS.Theater MS.Land MS.Book MS.Book.Program MS.Book.Convolve
open PowerSeries
open Fiscal BMenu Rider Reservoir VisitH Sea Fray FrameConj
open scoped BigOperators Topology Classical ContDiff
variable {G : Gauge}
local notation "BΨ" => Ensure.deck G
local notation "𝕄" => XSpace.Mesh
variable {n d : ℕ} {F H K x : Cn}

lemma root_sub (F x : Cn) (hx : Rooted x) : coeff 0 (F.subst x) = coeff 0 F := by
  rw [← pcomp]
  exact (congr_fun (Coupling.explicit hx F) 0).symm.trans (pay0 ..)

lemma assoc (h : Rooted H) (ht : Rooted K) (F : Cn) :
    PowerSeries.subst K (F.subst H) = F.subst (H.subst K) :=
  PowerSeries.subst_comp_subst_apply (Worried h) (Worried ht) _

lemma ups (p : ℕ → Point G d n) (h : Rooted F) (ht : Rooted H) :
    substitute H (substitute F p) = substitute (F.subst H) p := by
  apply byRanks
  intro v
  rw [readMove ht, readMove h, pcomp, pcomp, assoc h ht,
    readMove (show Rooted (F.subst H) from (root_sub F H ht).trans h), pcomp]

lemma earns (p : Reports G d) (h : Rooted F) (ht : Rooted H) :
    substitute H (substitute F p) = substitute (F.subst H) p := by
  ext1 n
  ext1 k
  ext1 t
  ext1 x
  have he : said (substitute H (substitute F p)) t x = said (substitute (F.subst H) p) t x := by
    rw [cite_r ht, cite_r h, pcomp, pcomp, assoc h ht,
      cite_r (show Rooted (F.subst H) from (root_sub F H ht).trans h), pcomp]
  obtain hp := congr_arg (coeff n) he
  simpa only [said, PowerSeries.coeff_mk] using hp

lemma retract (p : Reports G d) : substitute X p = p := by
  have ht : ∀ k (t : Test k) (x : Fin k → Sec G d), said (substitute X p) t x = said p t x :=
    fun k t x => by
    rw [cite_r
        (show Rooted X from
          (by
            unfold Rooted
            simp)),
      pcomp, PowerSeries.X_subst]
  ext1 n
  ext1 k
  ext1 t
  ext1 x
  obtain hp := congr_arg (coeff n) (ht k t x)
  simpa only [said, PowerSeries.coeff_mk] using hp

def Counter (F : Cn) :=
  if h : IsUnit (coeff 1 F) then PowerSeries.substInvOfIsUnit F h else PowerSeries.X

lemma born (F : Cn) : Rooted (Counter F) := by
  unfold Rooted
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  unfold Counter
  split_ifs <;> simp

lemma counter_l (h : Rooted F) (hp : coeff 1 F ≠ 0) : F.subst (Counter F) = X := by
  rw [Counter, dif_pos (isUnit_iff_ne_zero.mpr hp)]
  exact subst_substInvOfIsUnit_right F ((coeff_zero_eq_constantCoeff_apply F).symm.trans h) _

lemma counter_r (h : Rooted F) (hp : coeff 1 F ≠ 0) : (Counter F).subst F = X := by
  rw [Counter, dif_pos (isUnit_iff_ne_zero.mpr hp)]
  exact subst_substInvOfIsUnit_left F ((coeff_zero_eq_constantCoeff_apply F).symm.trans h) _

lemma eraser (U : Cn) : U.subst X = U := by rw [PowerSeries.X_subst]

lemma separate (h : Rooted F) (hp : coeff 1 F ≠ 0) (hx : Rooted H) (hv : Rooted K)
    (he : F.subst H = F.subst K) : H = K := by
  have ht := congr_arg (fun x => (Counter F).subst x) he
  rw [← assoc h hx, ← assoc h hv, counter_r h hp, PowerSeries.subst_X (Worried hx),
    PowerSeries.subst_X (Worried hv)] at ht
  exact ht
section growth

abbrev Tracks (p : 𝕄 → Cn) (Y : Cn) :=
  ∀ n, Fast (fun i => coeff n (p i)) (coeff n Y)
variable {p : 𝕄 → Cn} {Q : Cn}

lemma Coast (h : Tracks p Q) (n : ℕ) : Tracks (fun i => p i ^ n) (Q ^ n) := by
  induction n with
  | zero =>
    simp_rw [pow_zero]
    intro i
    exact Fast.const _
  | succ n ih =>
    intro i
    simp_rw [pow_succ, PowerSeries.coeff_mul]
    exact Fast.p_sum _ fun x _ => (ih _).mul (h _)

lemma Counter_next (h : Rooted Q) (hp : coeff 1 Q ≠ 0) {i : ℕ} (hi : i ≠ 0) :
    let S := Counter Q;
    coeff i S = (coeff i X - ∑ j ∈ (Finset.Iic i).erase 1, cut S j i * coeff j Q) / (coeff 1 Q) := by
  intro S
  rw [eq_div_iff hp]
  obtain hT := congr_arg (coeff i) (counter_l h hp)
  rw [usePool (c := Counter Q) (born Q), ←
    Finset.add_sum_erase _ _ (show 1 ∈ Finset.Iic i from Finset.mem_Iic.mpr (by omega)), cut,
    pow_one] at hT
  change coeff i S * coeff 1 Q + _ = _ at hT
  rw [← hT]
  simp only [S, add_sub_cancel_right]

lemma rootPrice {i t : ℕ} (hi : i ≠ 1) (hp : ∀ v : 𝕄, Rooted (p v)) (h : Rooted Q)
    (ht : ∀ n < t, Fast (fun v => coeff n (p v)) (coeff n Q)) :
    Fast (fun v => cut (p v) i t) (cut Q i t) := by
  have hd (n : ℕ) (j : ℕ) (hj : j < t) : Fast (fun v => cut (p v) n j) (cut Q n j) := by
    induction n generalizing j with
    | zero =>
      simp_rw [cut, pow_zero]
      exact Fast.const _
    | succ n ih =>
      unfold cut
      simp_rw [pow_succ, PowerSeries.coeff_mul]
      refine Fast.p_sum _ fun x hx => ?_
      obtain hv := Finset.mem_antidiagonal.mp hx
      exact (ih x.1 (by omega)).mul (ht x.2 (by omega))
  cases i with
  | zero =>
    simp_rw [cut, pow_zero]
    exact Fast.const _
  | succ i =>
    unfold cut
    simp_rw [pow_succ, coeff_mul]
    refine Fast.p_sum _ fun x hx => ?_
    obtain he := Finset.mem_antidiagonal.mp hx
    by_cases hh : x.2 = 0
    · simp_rw [hh, h, hp, mul_zero]
      exact Fast.const _
    by_cases hv : x.2 = t
    · have hs : x.1 = 0 := by omega
      simp_rw [hs]
      simp_rw [show coeff 0 (Q ^ i) = 0 from blocked h (by omega),
        show ∀ v : 𝕄, coeff 0 (p v ^ i) = 0 from fun v => blocked (hp v) (by omega), zero_mul]
      exact Fast.const _
    exact (hd i x.1 (by omega)).mul (ht x.2 (by omega))

lemma Counter_steady (h : ∀ v : 𝕄, Rooted (p v)) (hp : Rooted Q) (hq : Tracks p Q)
    (he : coeff 1 Q ≠ 0) : Tracks (fun i => Counter (p i)) (Counter Q) := by
  have hh : ∀ᶠ i in Front, coeff 1 (p i) ≠ 0 := (hq 1).limit.eventually (eventually_ne_nhds he)
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    by_cases hv : i = 0
    · subst i
      unfold Rooted at h hp
      simp_rw [show ∀ v : Cn, coeff 0 (Counter v) = 0 from born]
      exact Fast.const _
    let P := (Finset.Iic i).erase 1
    let B (q : Cn) := ∑ j ∈ P, cut (Counter q) j i * coeff j q
    have hP : Fast (fun i => B (p i)) (B Q) :=
      Fast.p_sum P fun j hj =>
        (rootPrice (Finset.mem_erase.mp hj |>.1) (fun v => born (p v)) (born Q) ih).mul (hq j)
    let v : ℂ := coeff i PowerSeries.X
    have hI : Fast (fun j => v - B (p j)) (v - B Q) := (Fast.const _).sub hP
    have hxC : Fast (fun i => (coeff 1 (p i))⁻¹) ((coeff 1 Q)⁻¹) :=
      Fast.mode (hq 1)
        (DifferentiableAt.inv (differentiableAt_id (𝕜 := ℝ) (x := coeff 1 Q)) (show id _ ≠ 0 from he))
    have hD : Fast (fun x => (v - B (p x)) / coeff 1 (p x)) ((v - B Q) / coeff 1 Q) := by
      simp_rw [div_eq_mul_inv]
      exact Fast.mul hI hxC
    rw [Counter_next hp he hv]
    exact hD.change (hh.mono fun v hv' => (Counter_next (h v) hv' hv).symm)
end growth
end YM.WilsonMS.Ice
