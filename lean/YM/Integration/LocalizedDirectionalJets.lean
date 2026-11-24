import YM.RG.Masks
import YM.Gauge.Chart

/-! Exact reduction of directional words to the links read by a cylindrical field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.LocalizedDirectionalJets

open Lattice Wilson RG
open scoped Classical BigOperators

variable {G : Gauge} {n : Side} {X : Type*}

def inside (P : Support n) (e : Edge (Site n)) : Prop := e.1 ∈ P ∧ e.1 + Lattice.step e.2 ∈ P

def field (P : Support n) (W U : Config G n) : Config G n :=
  fun e => if inside P e then U e else W e

def direction (P : Support n) (v : Directions G n) : Directions G n :=
  fun e => if inside P e then v e else 0

theorem agrees (P : Support n) (W U : Config G n) : Agrees P (field P W U) U := by
  intro e hr hs
  exact if_pos (show inside P e from ⟨hr,hs⟩)

theorem cylindrical (P : Support n) (W : Config G n) (F : Config G n → X) :
    LocalOn P (fun U => F (field P W U)) := by
  intro U V h
  apply congrArg F
  funext e
  by_cases he : inside P e
  · simpa only [field,if_pos he] using h e he.1 he.2
  · simp only [field,if_neg he]

theorem restore {P : Support n} (W : Config G n) {F : Config G n → X} (h : LocalOn P F) :
    (fun U => F (field P W U)) = F := by
  funext U
  exact h _ _ (agrees P W U)

theorem field_increment (P : Support n) (W U : Config G n) (t : ℝ) (v : Directions G n) :
    field P W (increment U (t • v)) = increment (field P W U) (t • direction P v) := by
  funext e
  by_cases he : inside P e <;> simp [field,direction,increment,he]

variable [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem jets (P : Support n) (W : Config G n) (F : Config G n → X) (l : List (Directions G n))
    (U : Config G n) :
    leftDerivs (fun z => F (field P W z)) l U = leftDerivs F (l.map (direction P)) (field P W U) := by
  induction l generalizing U with
  | nil => rfl
  | cons v l ih =>
    simp only [List.map_cons,leftDerivs]
    apply congrArg (fun h : ℝ → X => deriv h 0)
    funext t
    rw [ih,field_increment]

def envelope (q : BudgetPoint) (o : Site n) (P : Support n) (e : Edge (Site n)) : ℝ :=
  if inside P e then q.threshold * (1+(separation e.1 o : ℝ))^q.power else 0

theorem nonnegative (q : BudgetPoint) (o : Site n) (P : Support n) (e : Edge (Site n)) :
    0 ≤ envelope q o P e := by
  by_cases he : inside P e
  · simp only [envelope,if_pos he]
    exact mul_nonneg q.threshold_pos.le (by positivity)
  · simp only [envelope,if_neg he,le_refl]

theorem bounded (q : BudgetPoint) (o : Site n) (P : Support n) {v : Directions G n} (h : q.dirBound o v) :
    ∀ e, ‖direction P v e‖ ≤ envelope q o P e := by
  intro e
  by_cases he : inside P e
  · simpa only [direction,envelope,if_pos he] using h e
  · simp only [direction,envelope,if_neg he,norm_zero,le_refl]

theorem requested (q : BudgetPoint) (o : Site n) (P : Support n) (W : Config G n) (F : Config G n → X)
    {c : ℝ} (hc : 0 ≤ c) (hF : ∀ U l, l.length ≤ q.order →
      (∀ v ∈ l, ∀ e, ‖v e‖ ≤ envelope q o P e) → ‖leftDerivs F l U‖ ≤ c) :
    q.supBounds o P (fun U => F (field P W U)) c := by
  refine ⟨hc,fun U _ l hl hs => ?_⟩
  rw [jets]
  apply hF
  · simpa only [List.length_map] using hl
  · intro v hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv
    exact bounded q o P (hs a ha)

end YM.Integration.LocalizedDirectionalJets
end
