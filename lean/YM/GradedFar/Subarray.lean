import YM.XSpace.Playing
import YM.XSpace.Cart

/-! Under subtupling of a kernel, on both sides of the adjustment,
use the actual gates, sites family and formal orders.
-/
namespace YM.FVA2.GradedFar.Subarray
noncomputable section
open Filter Set Function PowerSeries
open XSpace XSpace.Normalize XSpace.Cirrus
open scoped Classical Topology BigOperators

variable {m n : ℕ} (e : Fin m ↪ Fin n)

def dates : Days m ↪ Days n :=
  ⟨Finsupp.embDomain e.optionMap, Finsupp.embDomain_injective _⟩
@[simp] lemma date_none (D : Days m) : (dates e D) none = D none := by
  change Finsupp.embDomain e.optionMap D (e.optionMap none) = _; rw [Finsupp.embDomain_apply_self]
@[simp] lemma date_at (D : Days m) (j : Fin m) : (dates e D) (some (e j)) = D (some j) := by
  change Finsupp.embDomain e.optionMap D (e.optionMap (some j)) = _; rw [Finsupp.embDomain_apply_self]
lemma date_vacant (D : Days m) {k : Fin n} (hk : k ∉ range e) : (dates e D) (some k) = 0 := by
  apply Finsupp.embDomain_notin_range
  rintro ⟨j,h⟩
  cases j with
  | none => contradiction
  | some j => exact hk ⟨j,Option.some.inj h⟩
lemma dates_tally {D : Days m} (j : ℕ) : dates e D ∈ tally j n ↔ D ∈ tally j m := by
  rw [totaled,totaled]
  change (∑ i, Finsupp.embDomain e.optionMap D i) = j ↔ _
  have h : (∑ i, Finsupp.embDomain e.optionMap D i) = ∑ i, D i := by
    let f := fun (_ : Option (Fin n)) (i : ℕ) => i
    have H := Finsupp.sum_embDomain (g:=f) (f:=e.optionMap) (v:=D)
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Finsupp.sum_fintype _ _ (fun _ => rfl)] at H
    exact H
  rw [h]
lemma dates_iff {D : Days n} (j : ℕ) :
    D ∈ Finset.map (dates e) (tally j m) ↔ D ∈ tally j n ∧ ∀ k ∉ range e, D (some k) = 0 := by
  constructor
  · intro h; obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp h; exact ⟨(dates_tally e j).2 hv,fun _ => date_vacant e v⟩
  rintro ⟨h,hv⟩
  let T := Finsupp.equivFunOnFinite.symm fun i => D (e.optionMap i)
  have he : dates e T = D := by
    ext k
    cases k with
    | none => rw [date_none]; simp [T]
    | some k => by_cases hr : k ∈ range e
                · obtain ⟨l,rfl⟩ := hr; rw [date_at]; simp [T]
                rw [date_vacant e T hr, hv k hr]
  rw [← he] at h ⊢
  exact Finset.mem_map.mpr ⟨T,(dates_tally e j).1 h,rfl⟩

theorem dates_sum {A : Type} [AddCommMonoid A] (F : Days n → A) (j : ℕ)
    (h : ∀ D ∈ tally j n, ∀ k ∉ range e, D (some k) ≠ 0 → F D = 0) :
    ∑ D ∈ tally j n, F D = ∑ t ∈ tally j m, F (dates e t) := by
  rw [← Finset.sum_map (tally j m)]
  refine Eq.symm (Finset.sum_subset (fun t ht => ((dates_iff e j).1 ht).1) ?_)
  intro x hx hr
  by_contra he
  exact hr ((dates_iff e j).2 ⟨hx,fun k hk => by_contra fun hv => he (h x hx k hk hv)⟩)

lemma dates_kernel {E : Type} [AddCommMonoid E] [Module ℂ E] {V : E}
    (x : Fin n → ℕ → E)
    (hx : ∀ k ∉ range e, ∀ j, x k j = if j=0 then V else 0)
    (F : ℕ → MultilinearMap ℂ (fun _ : Fin n => E) ℂ)
    (Q : ℕ → MultilinearMap ℂ (fun _ : Fin m => E) ℂ)
    (h : ∀ k (u : Fin n → E), (∀ i ∉ range e, u i = V) → F k u = Q k (u ∘ e)) (j : ℕ) :
    (∑ D ∈ tally j n, F (D none) (fun i => x i (D (some i)))) =
      ∑ T ∈ tally j m, Q (T none) (fun i => x (e i) (T (some i))) := by
  rw [dates_sum e (fun D => _) _ (fun D _ k hk hi => (F _).map_coord_zero (i:=k)
    (by rw [hx k hk _, if_neg hi]))]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [date_none, h _ _ (fun i hi => by rw [hx i hi _, date_vacant e t hi, if_pos rfl])]
  simp [comp_def]

lemma empty_tally (k : ℕ) : tally k 0 = {Finsupp.single none k} := by
  classical
  ext D
  have h : ∑ i, D i = D none := by rw [Fintype.sum_option]; simp
  rw [totaled, h, Finset.mem_singleton]
  constructor
  · intro p; apply Finsupp.ext; intro i; cases i with
    | none => simpa using p
    | some j => exact j.elim0
  rintro rfl; simp

lemma empty_slots {E : Type} [AddCommMonoid E] [Module ℂ E]
    (x : Fin 0 → ℕ → E) (v : Fin 0 → E) (F : ℕ → MultilinearMap ℂ (fun _ : Fin 0 => E) ℂ) (j : ℕ) :
    (∑ D ∈ tally j 0, F (D none) fun i => x i (D (some i))) = F j v := by
  rw [empty_tally,Finset.sum_singleton,Finsupp.single_eq_same]
  exact congrArg _ (Subsingleton.elim ..)

/-- Exact projection of the placements. No need to rechoose even the Mesh center. -/
def config (x : Points n) : Points m := points (x.ofLp ∘ e)

def sample (q : Sample n) : Sample m := ⟨q.F, q.layout ∘ e, q.center⟩
@[simp] lemma familiar_sample (p : Sample n) : familiar (sample e p) = config e (familiar p) := rfl
lemma config_continuous : Continuous (config e) :=
  (PiLp.continuous_toLp 2 (fun _: Fin m=> E4)).comp
    (continuous_pi (fun (i : Fin m) => (show Continuous (fun (x : Points n) => x (e i)) by fun_prop)))
theorem gate (x : Points n) : Tendsto (sample e) (Gate x) (Gate (config e x)) := by
  nth_rw 2 [Gate]; rw [tendsto_inf, tendsto_inf]
  exact ⟨⟨tendsto_comap_iff.mpr (liftG x), tendsto_comap_iff.mpr (((config_continuous e).tendsto x).comp (senseG x))⟩,
    tendsto_principal.mpr (welcomeG x)⟩
lemma configuration {x : Points n} (h : x ∈ conf n) : config e x ∈ conf m :=
  fun _ _ hu => e.injective (h hu)

/-- Kept Near and kept Far positions, ordered as the original implementation. -/
def joint {l k : ℕ} (u : Fin l ↪ Fin k) : Fin (m+l) ↪ Fin (n+k) :=
  finSumFinEquiv.symm.toEmbedding.trans ((e.sumMap u).trans finSumFinEquiv.toEmbedding)
@[simp] lemma keep_left {l k : ℕ} (u : Fin l ↪ Fin k) (i : Fin m) :
    joint e u (Fin.castAdd l i) = Fin.castAdd k (e i) := by simp [joint]
@[simp] lemma keep_right {l k : ℕ} (u : Fin l ↪ Fin k) (i : Fin l) :
    joint e u (Fin.natAdd m i) = Fin.natAdd n (u i) := by simp [joint]
lemma join {A : Type*} {l k : ℕ} (u : Fin l ↪ Fin k) (x : Fin n → A) (y : Fin k → A) :
    Fin.append x y ∘ joint e u = Fin.append (x ∘ e) (y ∘ u) := by
  funext i
  induction i using Fin.addCases <;> simp
lemma lonely {A : Type*} {l k : ℕ} (u : Fin l ↪ Fin k) (x : Fin n → A) (y : Fin k → A)
    (z : A) (hx : ∀ i ∉ range e, x i = z) (hy : ∀ i ∉ range u, y i = z) :
    ∀ i ∉ range (joint e u), Fin.append x y i = z := by
  intro i
  induction i using Fin.addCases with
  | left i =>
    intro h
    rw [Fin.append_left]; apply hx
    rintro ⟨j,rfl⟩; exact h ⟨Fin.castAdd l j,keep_left e u j⟩
  | right i =>
    intro h; rw [Fin.append_right]; apply hy
    rintro ⟨j,rfl⟩; exact h ⟨Fin.natAdd m j,keep_right e u j⟩

end
end YM.FVA2.GradedFar.Subarray
