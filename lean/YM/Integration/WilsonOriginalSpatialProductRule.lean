import YM.Integration.WilsonOriginalSupportedMixedJets

/-! Ordered real spatial derivatives on the interior of the filed box. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalSpatialProductRule
open Filter Set
open WilsonOriginalSupportedBoxChart (Space)
open scoped Topology ContDiff

def step {d : ℕ} (i : Fin d) (f : Space d → ℂ) : Space d → ℂ :=
  fun x => fderiv ℝ f x (Pi.single i (1:ℝ))

def word {d : ℕ} : List (Fin d) → (Space d → ℂ) → Space d → ℂ
  | [],f => f
  | i::t,f => word t (step i f)

theorem append {d : ℕ} (s t : List (Fin d)) (f : Space d → ℂ) :
    word (s++t) f = word t (word s f) := by
  induction s generalizing f with
  | nil => rfl
  | cons i s ih => exact ih (step i f)

theorem sampled {d : ℕ} (dir : ℕ → Fin d) (f : Space d → ℂ) (j : ℕ) :
    word (List.ofFn (fun k : Fin j => dir k.val)) f =
      WilsonOriginalSupportedMixedJets.derivative dir f j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [List.ofFn_succ',List.concat_eq_append,append]
    simp only [Fin.val_castSucc,Fin.val_last,ih]
    rfl

def Regular {d : ℕ} (O : Set (Space d)) (f : Space d → ℂ) : Prop :=
  ∀ x ∈ O, ContDiffAt ℝ ∞ f x

theorem regular_step {d : ℕ} {O : Set (Space d)} {f : Space d → ℂ} (sf : Regular O f)
    (i : Fin d) : Regular O (step i f) :=
  fun x hx => ((sf x hx).fderiv_right (m:=∞) (by simp)).clm_apply contDiffAt_const

theorem germ {d : ℕ} (s : List (Fin d)) (O : Set (Space d)) (ho : IsOpen O)
    {f g : Space d → ℂ} (eq : EqOn f g O) : EqOn (word s f) (word s g) O := by
  induction s generalizing f g with
  | nil => exact eq
  | cons i s ih =>
    apply ih
    intro x hx
    have nearby : f =ᶠ[𝓝 x] g := by
      filter_upwards [ho.mem_nhds hx] with y hy using eq hy
    change (fderiv ℝ f x) _ = (fderiv ℝ g x) _
    rw [nearby.fderiv_eq]

theorem plus {d : ℕ} (s : List (Fin d)) {O : Set (Space d)} (ho : IsOpen O)
    {f g : Space d → ℂ} (sf : Regular O f) (sg : Regular O g) :
    EqOn (word s (fun x => f x+g x)) (fun x => word s f x+word s g x) O := by
  induction s generalizing f g with
  | nil => exact fun _ _ => rfl
  | cons i s ih =>
    have once : EqOn (step i (fun x => f x+g x)) (fun x => step i f x+step i g x) O := by
      intro x hx
      simp only [step,fderiv_fun_add (sf x hx |>.differentiableAt (by simp)) (sg x hx |>.differentiableAt (by simp)),
        add_apply]
    exact (germ s O ho once).trans (ih (regular_step sf i) (regular_step sg i))

theorem original {d : ℕ} (s : List (Fin d)) (i : Fin d) {O : Set (Space d)} (ho : IsOpen O)
    {f g : Space d → ℂ} (sf : Regular O f) (sg : Regular O g) :
    EqOn (word (i::s) (fun x => f x*g x))
      (fun x => word s (fun y => step i f y*g y) x + word s (fun y => f y*step i g y) x) O := by
  have once : EqOn (step i (fun x => f x*g x)) (fun x => step i f x*g x+f x*step i g x) O := by
    intro x hx
    simp only [step,fderiv_fun_mul (sf x hx |>.differentiableAt (by simp)) (sg x hx |>.differentiableAt (by simp)),
      add_apply,smul_apply,smul_eq_mul]
    ring
  apply (germ s O ho once).trans
  exact plus s ho (fun x hx => (regular_step sf i x hx).mul (sg x hx))
    (fun x hx => (sf x hx).mul (regular_step sg i x hx))

end YM.Integration.WilsonOriginalSpatialProductRule
