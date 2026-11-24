import YM.Integration.WilsonMeasuredPublicEntrancePeers

/-! Ordered replacement through the regular peer u_X - e. Every occurrence
of the unreplaced trial enters the second sum with a marked occupied account.
The salaries in the first sum involve the physical regulars and the signed
settlement alone. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceCheapOrder
open scoped BigOperators

variable {V : Type*}

def route {K : Type*} [Semiring K] (upper lower edge : V → K) : List V → K
  | [] => 0
  | v :: vs => edge v * (vs.map upper).prod + lower v * route upper lower edge vs

theorem crossed (D : ℂ) (a b c : V → ℂ) (edge : ∀ v, D*(a v-b v)=c v)
    (vs : List V) :
    D*((vs.map a).prod - (vs.map b).prod) = route a b c vs := by
  induction vs with
  | nil => simp [route]
  | cons i is ih =>
    simp only [List.map_cons, List.prod_cons, route]
    rw [← edge i, ← ih]
    ring

theorem original (D : ℂ) (x y e hard : V → ℂ)
    (sheet : ∀ v, D*(y v-(x v-e v))=hard v) (vs : List V) :
    D*((vs.map x).prod - (vs.map y).prod) =
      D*route x (fun v => x v-e v) e vs - route y (fun v => x v-e v) hard vs := by
  have a := crossed (1:ℂ) x (fun v => x v-e v) e (by intro; ring) vs
  rw [one_mul] at a
  rw [← a, ← crossed D y (fun v => x v-e v) hard sheet vs]
  ring

theorem price (x e : V → ℂ) (n δ : V → ℝ)
    (px : ∀ v, ‖x v‖≤n v) (pe : ∀ v, ‖e v‖≤δ v) (vs : List V) :
    ‖route x (fun v => x v-e v) e vs‖ ≤ route n (fun v => n v+δ v) δ vs := by
  have mult (s : List V) : ‖(s.map x).prod‖ ≤ (s.map n).prod := by
    induction s with
    | nil => simp
    | cons i s ih =>
      simp only [List.map_cons, List.prod_cons, norm_mul]
      exact mul_le_mul (px i) ih (norm_nonneg _) ((norm_nonneg _).trans (px i))
  induction vs with
  | nil => simp [route]
  | cons i is ih =>
    simp only [route]
    apply (norm_add_le ..).trans
    simp only [norm_mul]
    have cheap := (norm_sub_le (x i) (e i)).trans (add_le_add (px i) (pe i))
    exact add_le_add (mul_le_mul (pe i) (mult is) (norm_nonneg _) ((norm_nonneg _).trans (pe i)))
      (mul_le_mul cheap ih (norm_nonneg _) ((norm_nonneg _).trans cheap))

end YM.Integration.WilsonMeasuredPublicEntranceCheapOrder
end
