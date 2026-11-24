import YM.Integration.ConditionalAffineLoadPrices

/-! A changed physical tree site kept on a propagated signed source column.
The location of its unique column is the actual tree site. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.PhysicalAffineScalarRootContraction
open Filter Function Set Matrix Lattice FreeResolvent FreeResolvent.Affine FreeResolvent.TestD FreeResolvent.Mark
open ConditionalAffineLoadPrices
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {c : Side} {ι κ : Type*} [Fintype ι] [Fintype κ]
local notation "E" => Vec G c 1
local notation "ray₀" => ray G c
local notation "D₀" => native c

structure Rooted (p : ι→Site c) (z : Site c) (δ C : ℝ) (n : ℕ) (F : E→ι→ℝ) : Prop where
  smooth : ContDiffAt ℝ n (column F) 0
  priced (l : List (raw G c)) (hl : l.length≤n) :
    (marks G c δ).Rates D₀ p (fun _ : Unit => z) l δ C (jet ray₀ (column F) l 0)

namespace Rooted
variable {p : ι→Site c} {q : κ→Site c} {z : Site c} {δ d γ C M N V : ℝ} {n : ℕ} {F H : FreeResolvent.Vec G c 1 → ι → ℝ}

private theorem scalar_smooth (s : ContDiffAt ℝ n (column F) 0) (i : ι) :
    ContDiffAt ℝ n (fun b => F b i) 0 :=
  (TestD.evaluate i ()).contDiff.contDiffAt.comp 0 s

private theorem mask_count {τ : Type*} (l : List τ) : Fintype.card (Masks l) = 2 ^ l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    change Fintype.card (Masks l ⊕ Masks l) = 2 ^ (l.length + 1)
    rw [Fintype.card_sum, ih, pow_succ]
    omega

theorem row (h : Rooted p z δ C n F) (l : List (raw G c)) (hl : l.length≤n) (i : ι) :
    (marks G c δ).pay l (p i)*((D₀).weight δ (p i) z*|jet ray₀ (column F) l 0 i ()|)≤C := by
  simpa only [Fintype.sum_unique] using (h.priced l hl).rows i

theorem sum (h : Rooted p z δ C n F) (h' : Rooted p z δ M n H) :
    Rooted p z δ (C+M) n (fun b => F b+H b) := by
  refine ⟨h.smooth.add h'.smooth,fun l hl => ?_⟩
  change (marks G c δ).Rates D₀ p (fun _ : Unit => z) l δ (C+M) (jet ray₀ (fun b => column F b + column H b) l 0)
  rw [jet_add ray₀ l (smooth_of_le h.smooth hl) (smooth_of_le h'.smooth hl)]
  exact (h.priced l hl).add (h'.priced l hl)

theorem diff (h : Rooted p z δ C n F) (h' : Rooted p z δ M n H) :
    Rooted p z δ (C+M) n (fun b => F b-H b) := by
  refine ⟨h.smooth.sub h'.smooth,fun l hl => ?_⟩
  change (marks G c δ).Rates D₀ p (fun _ : Unit => z) l δ (C+M) (jet ray₀ (fun b => column F b-column H b) l 0)
  rw [jet_sub ray₀ l (smooth_of_le h.smooth hl) (smooth_of_le h'.smooth hl),sub_eq_add_neg]
  exact (h.priced l hl).add (h'.priced l hl).neg

/-- A marked source column propagates through any already paid ordinary
rectangular kernel, retaining the changed site without a torus-volume factor. -/
theorem action (hF : Rooted p z δ C n F) (hC : 0≤C) {J : E→Matrix κ ι ℝ}
    (hJ : Bundle ray₀ (marks G c δ) D₀ q p J 0 n γ M) (hM : 0≤M) (hδ : 0≤δ) (hγ : δ+n*δ≤γ) :
    Rooted q z δ (2^n*(C*M)) n (fun b => J b *ᵥ F b) := by
  let P := marks G c δ
  have hs : column (fun b => J b *ᵥ F b) = fun b => J b*column F b := rfl
  refine ⟨by rw [hs]; exact prod_smooth hJ.smooth hF.smooth,fun l hl => ?_⟩
  rw [hs,jet_mul ray₀ l (smooth_of_le hJ.smooth hl) (smooth_of_le hF.smooth hl)]
  have h (m : Masks l) : P.Rates D₀ q (fun _ : Unit => z) l δ (C*M)
      (jet ray₀ J (lo l m) 0 * jet ray₀ (column F) (hi l m) 0) := by
    have hu := (len_high l m).trans hl
    have hlen : ((hi l m).length : ℝ) ≤ (n : ℝ) := by exact_mod_cast hu
    have H := (hJ.bound (lo l m) ((len_low l m).trans hl)).row.mul (position_move D₀ hearth hδ)
      zero_le_one hδ (show δ+(hi l m).length*δ≤γ from by
        linarith [mul_le_mul_of_nonneg_right hlen hδ])
      (P.pay_masks l m) (hF.priced (hi l m) hu) hC
    simpa only [one_pow,one_mul] using H
  have total (s : Finset (Masks l)) : P.Rates D₀ q (fun _ : Unit => z) l δ (∑ _m∈s, C*M)
      (∑ m∈s, jet ray₀ J (lo l m) 0 * jet ray₀ (column F) (hi l m) 0) := by
    induction s using Finset.induction_on with
    | empty =>
      simpa only [Finset.sum_empty] using
        (Mark.Rates.zero (C:=P) (D:=D₀) (a:=q) (b:=fun _ : Unit => z) (l:=l) (σ:=δ) (le_refl (0:ℝ)))
    | insert m s hm ih => simp only [Finset.sum_insert hm]; exact (h m).add ih
  have he : (∑ _m : Masks l, C*M)≤2^n*(C*M) := by
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mask_count,Nat.cast_pow,Nat.cast_ofNat]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) hl) (mul_nonneg hC hM)
  exact (total Finset.univ).mono le_rfl he

/-- The sole genuine changed covariance contracted with an ordinary source.
The volume charged by the original one-inverse estimate is displayed. -/
theorem inverse (hF : Paid p δ C n F) (hC : 0≤C) {A B : E→Matrix ι ι ℝ}
    (ha : ContDiffAt ℝ n A 0) (hb : ContDiffAt ℝ n B 0)
    (hH : ∀ l : List (raw G c), l.length≤n → Lever.Here ray₀ D₀ p hearth d γ z l M A B)
    (hM : 0≤M) (hδ : 0≤δ) (hd : δ≤d) (hγ : (n+1:ℕ)*δ≤γ) (hV : (D₀).Volume p δ V) (hv : 0≤V) :
    Rooted p z δ (2^n*(M*C*V)) n (fun b => (B b-A b)*ᵥ F b) := by
  have e : column (fun b => (B b-A b)*ᵥ F b) = fun b => (B b-A b)*column F b := rfl
  refine ⟨by rw [e]; exact prod_smooth (hb.sub ha) hF.smooth,fun l hl => ⟨fun i => ?_⟩⟩
  rw [e]
  simp only [Fintype.sum_unique]
  have h := ConditionalAffineRootContraction.apply_column hδ hd hγ hM hC hV ha hb hF.smooth hH hF.rows l hl i
  rw [mul_comm ((D₀).weight ..) ((marks G c δ).pay ..)] at h
  exact (mul_assoc ..).symm.le.trans (h.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) hl) (mul_nonneg (mul_nonneg hM hC) hv)))

/-- The final componentwise product carries the same true tag on one factor.
The per-row marked price has no summation over unanchored coordinates. -/
theorem product (hF : Rooted p z δ C n F) (hH : Paid p δ M n H) (hC : 0≤C) (hM : 0≤M) :
    Rooted p z δ (2^n*(C*M)) n (fun b i => F b i * H b i) := by
  let P := marks G c δ
  have hF' (i : ι) : ContDiffAt ℝ n (fun b => F b i) 0 := scalar_smooth hF.smooth i
  have hH' (i : ι) : ContDiffAt ℝ n (fun b => H b i) 0 := scalar_smooth hH.smooth i
  have sm : ContDiffAt ℝ n (column (fun b i => F b i * H b i)) 0 := TestD.rectangle_smooth fun i _ => (hF' i).mul (hH' i)
  refine ⟨sm,fun l hl => ⟨fun i => ?_⟩⟩
  simp only [Fintype.sum_unique]
  rw [←TestD.entry ray₀ l (smooth_of_le sm hl) i ()]
  change P.pay l (p i)*((D₀).weight δ (p i) z * |jet ray₀ (fun b => F b i*H b i) l 0|)≤_
  have hjet := leibniz ray₀ (ContinuousLinearMap.mul ℝ ℝ) l (smooth_of_le (hF' i) hl) (smooth_of_le (hH' i) hl)
  change jet ray₀ (fun b => F b i*H b i) l 0 = ∑ m : Masks l,
    jet ray₀ (fun b => F b i) (lo l m) 0 * jet ray₀ (fun b => H b i) (hi l m) 0 at hjet
  rw [hjet,←mul_assoc]
  let w := P.pay l (p i)*(D₀).weight δ (p i) z
  have hw : 0≤w := mul_nonneg (P.pay_pos ..).le ((D₀).weight_nn ..)
  calc
    _ ≤ w*∑ m : Masks l, |jet ray₀ (fun b => F b i) (lo l m) 0 * jet ray₀ (fun b => H b i) (hi l m) 0| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs ..) hw
    _ = ∑ m : Masks l, w*|jet ray₀ (fun b => F b i) (lo l m) 0 * jet ray₀ (fun b => H b i) (hi l m) 0| := Finset.mul_sum ..
    _ ≤ ∑ _m : Masks l, C*M := by
      apply Finset.sum_le_sum; intro m _
      have h₁ := (len_low l m).trans hl
      have h₂ := (len_high l m).trans hl
      have h₃ := hF.row (lo l m) h₁ i
      have h₄ := hH.rows (hi l m) h₂ i
      rw [←TestD.entry ray₀ (lo l m) (smooth_of_le hF.smooth h₁) i ()] at h₃
      rw [←TestD.entry ray₀ (hi l m) (smooth_of_le hH.smooth h₂) i ()] at h₄
      rw [show w = (P.pay (lo l m) (p i)*P.pay (hi l m) (p i))*(D₀).weight δ (p i) z by rw [←P.pay_masks],abs_mul]
      convert mul_le_mul h₃ h₄ (mul_nonneg (P.pay_pos ..).le (abs_nonneg _)) hC using 1
      dsimp only [P,column]
      ring
    _ ≤ _ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mask_count,Nat.cast_pow,Nat.cast_ofNat]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) hl) (mul_nonneg hC hM)

/-- Translate a genuine rooted signed scalar at fixed o. Exactly the rows
whose position is o are summed. A native spatial Volume pays their number. -/
theorem translated (hF : Rooted p z δ C n F) (hC : 0≤C) (hV : (D₀).Volume p d V)
    (o : Site c) (l : List (raw G c)) (hl : l.length≤n) :
    (marks G c δ).pay l o * ((D₀).weight δ o z *
      |jet ray₀ (fun b => ∑ i : ι, if p i=o then F b i else 0) l 0|) ≤ V*C := by
  let s := Finset.univ.filter (fun i : ι => p i=o)
  let P := marks G c δ
  have e : (fun b => ∑ i : ι, if p i=o then F b i else 0) = fun b => ∑ i∈s, F b i := by
    funext b; rw [Finset.sum_filter]
  have h (i : ι) : ContDiffAt ℝ l.length (fun b => F b i) 0 :=
    smooth_of_le (scalar_smooth hF.smooth i) hl
  rw [e,jet_sum ray₀ l s (fun i b => F b i) (fun i _ => h i),←mul_assoc]
  let w := P.pay l o * (D₀).weight δ o z
  have hw : 0≤w := mul_nonneg (P.pay_pos ..).le ((D₀).weight_nn ..)
  have count : (s.card:ℝ) ≤ V := by
    calc
      _ = ∑ _i∈s, (1:ℝ) := by simp
      _ = ∑ i∈s, (D₀).weight (-d) o (p i) := Finset.sum_congr rfl fun i hi => by
        have hp : p i=o := (Finset.mem_filter.mp hi).2; simp only [hp,Cost.weight_self]
      _ ≤ ∑ i : ι, (D₀).weight (-d) o (p i) := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun i _ _ => (D₀).weight_nn ..)
      _ ≤ V := hV.bound o
  calc
    _ ≤ w*∑ i∈s, |jet ray₀ (fun b => F b i) l 0| := mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs ..) hw
    _ = ∑ i∈s, w*|jet ray₀ (fun b => F b i) l 0| := Finset.mul_sum ..
    _ ≤ ∑ _i∈s, C := Finset.sum_le_sum fun i hi => by
      have hp : p i=o := (Finset.mem_filter.mp hi).2
      have hx := hF.row l hl i
      rw [hp,←TestD.entry ray₀ l (smooth_of_le hF.smooth hl) i (),←mul_assoc] at hx
      exact hx
    _ ≤ _ := by simpa only [Finset.sum_const,nsmul_eq_mul] using mul_le_mul_of_nonneg_right count hC

/-- Multiplication by the inverse spatial weight makes an ordinary source
into a rooted one at any fixed physical site. At that site the source is
unchanged, so the previously purchased rooted product and translation
are also authentic undifferenced estimates. -/
def localized (p : ι→Site c) (o : Site c) (δ : ℝ) (F : E→ι→ℝ) (b : E) (i : ι) :=
  (D₀).weight (-δ) (p i) o*F b i

theorem locate (h : Paid p δ C n F) (o : Site c) : Rooted p o δ C n (localized p o δ F) := by
  have hs (i : ι) : ContDiffAt ℝ n (fun b => F b i) 0 := scalar_smooth h.smooth i
  have sm : ContDiffAt ℝ n (column (localized p o δ F)) 0 := TestD.rectangle_smooth fun i _ =>
    contDiffAt_const.mul (hs i)
  refine ⟨sm,fun l hl => ⟨fun i => ?_⟩⟩
  simp only [Fintype.sum_unique]
  rw [←TestD.entry ray₀ l (smooth_of_le sm hl) i ()]
  change _*((D₀).weight δ (p i) o*|jet ray₀ (fun b => (D₀).weight (-δ) (p i) o*F b i) l 0|)≤_
  have he := jet_linear ray₀ l ((D₀).weight (-δ) (p i) o • ContinuousLinearMap.id ℝ ℝ) (smooth_of_le (hs i) hl)
  change jet ray₀ (fun b => (D₀).weight (-δ) (p i) o*F b i) l 0 = (D₀).weight (-δ) (p i) o*jet ray₀ (fun b => F b i) l 0 at he
  rw [he,abs_mul,abs_of_nonneg ((D₀).weight_nn ..),(D₀).weight_neg,←mul_assoc ((D₀).weight δ (p i) o) _ _,mul_inv_cancel₀ ((D₀).weight_pos ..).ne',one_mul]
  have hh := h.rows l hl i
  rw [←TestD.entry ray₀ l (smooth_of_le h.smooth hl) i ()] at hh
  exact hh

theorem ordinary_product (hF : Paid p δ C n F) (hH : Paid p δ M n H) (hC : 0≤C) (hM : 0≤M) :
    Paid p δ (2^n*(C*M)) n (fun b i => F b i*H b i) := by
  have hs (i : ι) := ((scalar_smooth hF.smooth i).mul
    (scalar_smooth hH.smooth i))
  have sm : ContDiffAt ℝ n (column (fun b i => F b i*H b i)) 0 := TestD.rectangle_smooth fun i _ => hs i
  refine ⟨sm,fun l hl i => ?_⟩
  have h := (locate hF (p i)).product hH hC hM
  have hx := h.row l hl i
  rw [Cost.weight_self,one_mul,←TestD.entry ray₀ l (smooth_of_le h.smooth hl) i ()] at hx
  rw [←TestD.entry ray₀ l (smooth_of_le sm hl) i ()]
  simpa only [column,localized,Cost.weight_self,one_mul] using hx

theorem ordinary_root (h : Paid p δ C n F) (hC : 0≤C) (hV : (D₀).Volume p d V) (o : Site c)
    (l : List (raw G c)) (hl : l.length≤n) :
    (marks G c δ).pay l o*|jet ray₀ (fun b => ∑ i : ι, if p i=o then F b i else 0) l 0|≤V*C := by
  have hx := (locate h o).translated hC hV o l hl
  have e : (fun b => ∑ i : ι, if p i=o then localized p o δ F b i else 0)=
      fun b => ∑ i : ι, if p i=o then F b i else 0 := by
    funext b; refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : p i=o <;> simp [hi,localized]
  simpa only [e,Cost.weight_self,one_mul] using hx

/-- A scalar with a genuine fixed numerical coefficient on the original
translation group is smoothly priced before or after taking its field jets. -/
theorem scaled_ordinary (h : Paid p δ C n F) (hC : 0≤C) (hV : (D₀).Volume p d V)
    (o : Site c) (α : ℝ) (Q : E→ℝ) (hq : Q=ᶠ[𝓝 0] fun b => α*∑ i : ι, if p i=o then F b i else 0)
    (l : List (raw G c)) (hl : l.length≤n) : ContDiffAt ℝ n Q 0 ∧
    (marks G c δ).pay l o*|jet ray₀ Q l 0|≤|α| * (V*C) := by
  let H := fun b : E => ∑ i : ι, if p i=o then F b i else 0
  have hs : ContDiffAt ℝ n H 0 := by
    apply ContDiffAt.sum; intro i _; by_cases hi : p i=o
    · simp only [hi,if_true]; exact scalar_smooth h.smooth i
    · simp only [hi,if_false]; exact contDiffAt_const
  refine ⟨(contDiffAt_const.mul hs).congr_of_eventuallyEq hq,?_⟩
  have h₀ : jet ray₀ Q l 0=jet ray₀ (fun b => α*H b) l 0 := by
    change iteratedFDeriv ℝ l.length _ 0 _=iteratedFDeriv ℝ l.length _ 0 _
    rw [(hq.iteratedFDeriv (𝕜:=ℝ) l.length).self_of_nhds]
  have h₁ : jet ray₀ Q l 0=α*jet ray₀ H l 0 := h₀.trans (jet_linear ray₀ l (α • ContinuousLinearMap.id ℝ ℝ) (smooth_of_le hs hl))
  rw [h₁,abs_mul,mul_left_comm]
  exact mul_le_mul_of_nonneg_left (ordinary_root h hC hV o l hl) (abs_nonneg α)

end Rooted
section Rows
open RG Next.SectorChange Next.SectorChange.Rows PhysicalAffineScalarOrdinaryColumns
variable {f : Side} (S : StepData c f)

/-- The original total physical row multiplicity and decay for a single
translation, uniform in the coarse or fine period. -/
def physicalVolume (G : Gauge) (L : Side) (t : ℝ) :=
  (Fintype.card Signed:ℝ)*(torusPay (Bloch.Co L (PAC G 2)) t +
    (torusPay (Bloch.Co L (PAC G 2)) t + torusPay (PAC G 1) t))

theorem row_volume (t : ℝ) (ht : 0<t) : (native c).Volume
    (PhysicalAffineScalarComparison.rowRoot (G:=G) S) t (physicalVolume G S.patch.L t) := by
  constructor; intro o
  let w := fun i : Rows.Receipt G S => (native c).weight (-t) o (PhysicalAffineScalarComparison.rowRoot S i)
  change ∑ i, w i≤_
  rw [rows_sum w]
  have h₁ (s : Signed) : (∑ i : tile G f, w (directRow (S:=S) s i))≤torusPay (Bloch.Co S.patch.L (PAC G 2)) t := by
    simpa only [w,←direct_anchor] using (named_volume (G:=G) S s 2 t ht).bound o
  have h₂ (s : Signed) : (∑ i : tile G f, w (ConditionalAffineRowDifference.row s i))≤
      torusPay (Bloch.Co S.patch.L (PAC G 2)) t := by
    simpa only [w,transported_anchor] using (named_volume (G:=G) S s 2 t ht).bound o
  have h₃ (s : Signed) : (∑ i : raw G c, w (predictorRow (S:=S) s i))≤torusPay (PAC G 1) t := by
    simpa only [w,←predictor_anchor] using (co_volume G c s 1 t ht).bound o
  exact (Finset.sum_le_sum fun s _ => add_le_add (h₁ s) (add_le_add (h₂ s) (h₃ s))).trans_eq
    (by simp [physicalVolume,mul_add])
end Rows
end YM.Integration.PhysicalAffineScalarRootContraction
end
