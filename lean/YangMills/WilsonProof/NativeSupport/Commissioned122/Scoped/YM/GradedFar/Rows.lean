import YM.FVA2.O.Score.Art
import Mathlib.LinearAlgebra.Multilinear.Curry

/-!
# Rows on the *actual* power-series correlation book

Choose a common cap for each row. Always expand the running conversion
on all Far legs at the same positions (incl. in center replacement rows).
Multilinear on the *input* labels of their own caps, which are in the
unconverted, constant basis. Uses `Sec`, i.e. the on-shell inputs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar
open Function XSpace XSpace.Normalize XSpace.Structure1 PowerSeries
open Scale O.Score MS.Book.Program Dframe
open scoped Classical BigOperators

variable {G : Gauge} {n m H d e h : ℕ}

/-- Length factor `exp(-η)`, Far conversion `K_η(t)` (formal series in the position
coupling; we'll pass η equal to -log T, and `B` is `GroupS.gaugeN`). -/
def transfer (B : ℝ → Frames G) (η : ℝ) (d : ℕ) : Guard G d :=
  C (Level.Dial d η) * B η d

lemma transfer_apply (B : ℝ → Frames G) (η : ℝ) (i : ℕ) (u : Sec G d) :
    coeff i (transfer B η d) u = Level.Dial d η (coeff i (B η d) u) := by
  rw [transfer, coeff_C_mul, Module.End.mul_apply]

lemma transfer_walk (B : ℝ → Frames G) (η : ℝ) (h : Civil (B η)) (he : d ≤ e) :
    Scale.Walk he (transfer B η d) (transfer B η e) := by
  intro i x; rw [transfer_apply, transfer_apply, h.growth he, Level.chain]

lemma transfer_unit (B : ℝ → Frames G) (η : ℝ) (h : Base (B η d)) (i : ℕ) :
    coeff i (transfer B η d) (leaf G d) = if i=0 then leaf G d else 0 := by
  rw [transfer_apply]; split
  · rename_i h'; subst i; rw [h.zero, Module.End.one_apply, Level.Dial_leaf]
  · rename_i h'; rw [show coeff i (B η d) (leaf G d)=0 from (h.high _ h').1, map_zero]

/-- Fixed scale evaluation of the multilinear coefficient. Standard extension by 0
outside configurations. (Our inequalities will be on separated configurations.) -/
def extAt (V : Arenas G) (x : Points n) (d i : ℕ) : Point G d n :=
  if hx : x ∈ conf n then V d n ⟨x,hx⟩ i else 0

lemma extAt_at (V : Arenas G) {x : Points n} (hx : x ∈ conf n) (d i : ℕ) :
    extAt V x d i = V d n ⟨x,hx⟩ i := dif_pos hx

lemma coeff_install_eq (V : Arenas G) (x : Points n) (he : Regular V) (v : Scan G n)
    (hv : Guarded v d) (i : ℕ) :
    coeff i (install V n x v) = extAt V x d i (tape v hv) := by
  by_cases hx : x ∈ conf n
  · rw [caring v hv he hx, extAt_at V hx]
    exact coeff_mk ..
  · unfold install extAt; rw [dif_neg hx, dif_neg hx, map_zero]; rfl

lemma extAt_lift (V : Arenas G) (x : Points n) (he : Regular V) (hd : d ≤ e) (i : ℕ)
    (v : Fin n → Sec G d) : extAt V x d i v = extAt V x e i (up hd ∘ v) := by
  unfold extAt; split
  · exact he d e hd n _ i v
  · rfl

/-- Regard first n slots as Near (incl. n=1 for replacement), remaining m as Far. -/
def curried (P : Point G H (n+m)) :
    MultilinearMap ℂ (fun _ : Fin n => Sec G H) (Point G H m) :=
  (P.domDomCongr (finSumFinEquiv.symm : Fin (n+m) ≃ Fin n ⊕ Fin m)).currySum

lemma curried_apply (P : Point G H (n+m)) (u : Fin n → Sec G H) (v : Fin m → Sec G H) :
    curried P u v = P (Fin.append u v) := by
  rw [curried, MultilinearMap.currySum_apply', MultilinearMap.domDomCongr_apply]
  apply congr_arg; funext i; induction i using Fin.addCases <;> simp

abbrev Appointed122Fields (G : Gauge) (d : Fin n → ℕ) := (i : Fin n) → Sec G (d i)
abbrev Form (G : Gauge) (d : Fin n → ℕ) (E : Type) [AddCommMonoid E] [Module ℂ E] :=
  MultilinearMap ℂ (fun i : Fin n => Sec G (d i)) E
abbrev Covered (d : Fin n → ℕ) (H : ℕ) := ∀ i, d i ≤ H

variable {d : Fin n → ℕ} {e : Fin m → ℕ} (V : Arenas G)

/-- A mixed cap request to extAt. We may precompose any linear change of labels,
independently on the Far legs. View as multilinear in the Near legs, valued
in the m-multilinear Far responses. -/
def mix (z : Points (n+m)) (j : ℕ) (hd : Covered d H) (he : Covered e H)
    (l : ∀ i, FieldEnd G (e i)) : Form G d (Form G e ℂ) :=
  (MultilinearMap.compLinearMapₗ (fun i : Fin m => up (he i) ∘ₗ l i)).compMultilinearMap
    ((curried (extAt V z H j)).compLinearMap fun i : Fin n => up (hd i))

lemma mix_apply (z : Points (n+m)) (j : ℕ) (hd : Covered d H) (he : Covered e H)
    (l : ∀ i, FieldEnd G (e i)) (u : Appointed122Fields G d) (v : Appointed122Fields G e) :
    mix V z j hd he l u v = extAt V z H j
      (Fin.append (fun i => up (hd i) (u i)) (fun i => up (he i) (l i (v i)))) := by
  simp only [mix, LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMapₗ_apply, MultilinearMap.compLinearMap_apply, LinearMap.comp_apply, curried_apply]

/-- Apply power-series changes of field to all Far inputs. `tally`: n-independent,
allocates k among correlation order and each of the m Far fields. -/
def ordered (C : ∀ i, Guard G (e i)) (z : Points (n+m)) (hd : Covered d H) (he : Covered e H)
    (k : ℕ) : Form G d (Form G e ℂ) :=
  ∑ j ∈ Normalize.tally k m,
    mix V z (j none) hd he (fun i => coeff (j (some i)) (C i))

lemma ordered_apply (C : ∀ i, Guard G (e i)) (z : Points (n+m)) (hd : Covered d H)
    (he : Covered e H) (k : ℕ) (u : Appointed122Fields G d) (v : Appointed122Fields G e) :
    ordered V C z hd he k u v = ∑ j ∈ Normalize.tally k m, extAt V z H (j none)
      (Fin.append (fun i => up (hd i) (u i))
        (fun i => up (he i) (coeff (j (some i)) (C i) (v i)))) := by
  unfold ordered; simp only [_root_.sum_apply, mix_apply]

lemma ordered_lift (C : ∀ i, Guard G (e i)) (z : Points (n+m)) (hd : Covered d H) (he : Covered e H)
    (hg : Regular V) {J : ℕ} (hJ : H ≤ J) (k : ℕ) :
    ordered V C z hd he k = ordered V C z (fun i => (hd i).trans hJ) (fun i => (he i).trans hJ) k := by
  ext1 u; ext1 v
  rw [ordered_apply, ordered_apply]; refine Finset.sum_congr rfl fun i _ => ?_
  rw [extAt_lift V _ hg hJ]; apply congr_arg; funext j
  induction j using Fin.addCases <;> simp only [Function.comp_apply, Fin.append_left, Fin.append_right] <;> rfl

-- Domain is covered by the products of the full spaces through each cap, not
-- by a restrictive budget that trades input price for distance or approximation order.
abbrev Words (G : Gauge) (d : Fin n → ℕ) := (i : Fin n) → Toon G (d i)
def filedMultipliers122 (u : Appointed122Fields G d) (i : Words G d) : ℂ := ∏ j : Fin n, coord (i j) (u j)
def basisFields (i : Words G d) : Appointed122Fields G d := fun j => theory (i j)
def labeling (i : Words G d) : Scan G n := fun j => Dframe.flash (i j)

/-- `R=1`: the unit polydiscs, using fixed basis coordinates (as allowed in §B
of the natural-language proof). See `multiplier_budget`. -/
def FieldBudget (u : Appointed122Fields G d) (R : ℝ) : Prop := ∀ i : Fin n, ∀ j : Toon G (d i),
  ‖coord j (u i)‖ ≤ R

/-- Fixed norms for statements involving finite field horizons. -/
abbrev Account (G : Gauge) (d : ℕ) := Toon G d → ℂ
noncomputable def account (G : Gauge) (d : ℕ) : Sec G d ≃ₗ[ℂ] Account G d :=
  (MS.Theater.Daylight (Press.portDeck G) d).equivFun
lemma account_entry (d : ℕ) (u : Sec G d) (i : Toon G d) :
    account G d u i = coord i u := rfl
lemma fieldBudget_iff (u : Appointed122Fields G d) {R : ℝ} (hr : 0 ≤ R) :
    FieldBudget u R ↔ ∀ i : Fin n, ‖account G (d i) (u i)‖ ≤ R := by
  simp_rw [pi_norm_le_iff_of_nonneg hr, account_entry]; rfl

lemma basis_budget (i : Words G d) : FieldBudget (basisFields i) 1 := by
  intro j k; rw [basisFields, pivotδ]; split <;> simp

lemma multiplier_budget (u : Appointed122Fields G d) {R : ℝ} (hv : FieldBudget u R)
    (i : Words G d) : ‖filedMultipliers122 u i‖ ≤ R^n := by
  unfold filedMultipliers122; rw [norm_prod]; exact (Finset.prod_le_prod
    (fun _ _ => norm_nonneg _) (fun j _ => hv j (i j))).trans_eq (by simp)

lemma multiplier_basis (i j : Words G d) : filedMultipliers122 (basisFields i) j = if i=j then 1 else 0 := by
  unfold filedMultipliers122 basisFields; simp_rw [pivotδ]; split
  · rename_i h; subst i; simp
  · rename_i h; obtain ⟨k,hk⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (i:=k) (Finset.mem_univ k) (if_neg hk)

/-- Expansion in the complete finite-horizon field basis. -/
lemma decompose_form {E : Type} [AddCommMonoid E] [Module ℂ E]
    (P : Form G d E) (u : Appointed122Fields G d) : P u = ∑ i : Words G d,
    filedMultipliers122 u i • P (basisFields i) := by
  have a (j : Fin n) : u j = ∑ k : Toon G (d j), coord k (u j) • theory k := (all_sig (u j)).symm
  have h := P.map_sum (fun i (k : Toon G (d i)) => coord k (u i) • theory k)
  simp_rw [← a] at h; rw [h]; refine Finset.sum_congr rfl fun i _ => ?_
  exact P.map_smul_univ _ _

/-- The series operand (z will be the positions including already dilated Far
points, in `G^X`'s argument units). -/
def series (B : ℝ → Frames G) (η : ℝ) (z : Points (n+m)) (hd : Covered d H) (he : Covered e H)
    (u : Appointed122Fields G d) (v : Appointed122Fields G e) : PowerSeries ℂ :=
  PowerSeries.mk (fun k => ordered V (fun i => transfer B η (e i)) z hd he k u v)

variable (B : ℝ → Frames G) (η : ℝ) (z : Points (n+m)) (hd : Covered d H) (he : Covered e H)
    (u : Appointed122Fields G d) (v : Appointed122Fields G e)
lemma series_lift (hr : Regular V) {J : ℕ} (hJ : H ≤ J) :
    series V B η z hd he u v =
    series V B η z (fun i => (hd i).trans hJ) (fun i => (he i).trans hJ) u v := by
  unfold series; simp_rw [ordered_lift V _ _ _ _ hr hJ]

lemma series_coeff (k : ℕ) : coeff k (series V B η z hd he u v) =
    ordered V (fun i => transfer B η (e i)) z hd he k u v := coeff_mk ..

lemma decompose_near : series V B η z hd he u v = ∑ i : Words G d,
    PowerSeries.C (filedMultipliers122 u i) * series V B η z hd he (basisFields i) v := by
  ext k
  rw [series_coeff, map_sum]; simp_rw [coeff_C_mul, series_coeff]; rw [decompose_form _ u]
  simp only [_root_.sum_apply, _root_.smul_apply, smul_eq_mul]

lemma decompose_far : series V B η z hd he u v = ∑ i : Words G e,
    PowerSeries.C (filedMultipliers122 v i) * series V B η z hd he u (basisFields i) := by
  ext k; rw [series_coeff, map_sum]; simp_rw [coeff_C_mul, series_coeff]; exact decompose_form _ v

/-- Center replacement row as a function of the label at horizon h. -/
def rowsResponse122 (V : Arenas G) (B : ℝ → Frames G) (η : ℝ) (z : Points (1+m)) (h : ℕ)
    (hh : h ≤ H) (he : Covered e H) (v : Appointed122Fields G e) (a : Sec G h) : PowerSeries ℂ :=
  series V B η z (d := fun _ : Fin 1 => h) (fun _ => hh) he (fun _ => a) v

lemma response_sum (z : Points (1+m)) (hh : h ≤ H) (g : Toon G h → ℂ) :
    rowsResponse122 V B η z h hh he v (∑ i, g i • theory i) = ∑ i : Toon G h,
      PowerSeries.C (g i) * rowsResponse122 V B η z h hh he v (theory i) := by
  ext k
  let L : Sec G h →ₗ[ℂ] Form G e ℂ :=
    (MultilinearMap.ofSubsingleton ℂ _ _ (0 : Fin 1)).symm
      (ordered V (fun i => transfer B η (e i)) z (d := fun _ : Fin 1 => h) (fun _ => hh) he k)
  have hL (a : Sec G h) : coeff k (rowsResponse122 V B η z h hh he v a) = L a v := by
    rw [rowsResponse122, series_coeff]; rfl
  rw [hL, map_sum, map_sum]; simp_rw [coeff_C_mul, hL, map_smul]; simp only [_root_.sum_apply, _root_.smul_apply]; rfl

end YM.FVA2.GradedFar
