import YM.Integration.WilsonLongContactAddress
import YM.RG16.Unmasked.Purchased

/-! The actual regular and forced budgets of a reported coefficient. Its complete complex
regular entry can occupy one marked mode in the full older Wilson law. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonLongContactStock
open Lattice Wilson RG Source Labels Marker MergeProof LocalLTE
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus PhysicalNext.Repeat.Legato
open MeasureTheory Progress.DirectedRecipe
open scoped Classical BigOperators
variable {G : Gauge} {d : ℕ} {F : Frame G d} (A : Run G) (simple : G.Simple)
variable {N per j : ℕ}

def Stock (P : Coefficient F (A.family.S.side j per)) (z : Site (A.family.S.side j per))
    (e : ℕ → ℝ) : Prop :=
  ∀ (V : Type) [DecidableEq V] (J : Census V) (s : J.Mode), s.val.Nonempty →
    ∀ i copy : ℕ, ∃ X : RegularAddress (A.family.S.side j per), X.site = z ∧ X.support = P.support i ∧
      ∃ L : Bool → Menu.Hat J (A.family.path.rep N per j),
        (∀ k, (L k).s = s ∧ (L k).M.turn = .logKey (blankRow _ (X,copy)) ∧
          (L k).M.crest = P.support i ∧ (L k).M.weight = e i ∧
          ∀ U, (L k).M.ingredient U = Port.scaleQ k (P.maskedTerm (A.family.path.rep N per j) i U)) ∧
        ∀ U, (∑ k : Bool, (((L k).M.cicada U : ℝ) : ℂ) * Port.ink k) =
          (A.family.path.rep N per j).eval U * P.maskedTerm (A.family.path.rep N per j) i U

include simple in
theorem original (hj : j ≤ N) (P : Coefficient F (A.family.S.side j per))
    (z : Site (A.family.S.side j per)) (H : Hol G)
    (format : P.Format z H (A.family.path.rep N per j)) {κ budget : ℝ}
    (paid : P.remBound z (A.family.path.rep N per j) κ budget) :
    let Q := A.family.path.rep N per j
    ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ a+b ≤ budget ∧ 0 < κ ∧
      ∃ e hard : ℕ → ℝ, SumBudget (fun i => Q.p.mass (P.support i) (e i)) a ∧
        SumBudget (fun i => Q.p.mass (Q.activities.forced i).support (hard i)) (κ*b) ∧
        (∀ i, 0 ≤ hard i ∧ ∀ U, ‖P.forced i U‖ ≤ hard i) ∧ Stock A (N:=N) P z e := by
  classical
  intro Q
  obtain ⟨a,b,ha,hb,hcost,hκ,⟨e,regular,he⟩,⟨hard,forced,hh⟩⟩ := paid
  refine ⟨a,b,ha,hb,hcost,hκ,e,hard,regular,forced,hh,?_⟩
  intro V _ J s hs i copy
  let X : RegularAddress _ := ⟨z,P.support i,format.origin i⟩
  choose L mode address support weight read _ allGas using
    fun k => WilsonLongContactAddress.filed A simple N per j hj z J s hs X copy
      (P.regular i) (e i) (format.smooth i) (he i) k
  refine ⟨X,rfl,rfl,L,fun k => ⟨mode k,address k,support k,weight k,congrFun (read k)⟩,?_⟩
  intro U
  have ke (k : Bool) : ((L k).M.cicada U : ℂ) * Port.ink k =
      (Q.eval U : ℂ) * ((Port.scaleQ k (P.maskedTerm Q i U) : ℂ) * Port.ink k) := by
    rw [allGas k U,Complex.ofReal_mul]
    change (Port.scaleQ k (P.maskedTerm Q i U) : ℂ) * (Q.eval U : ℂ) * Port.ink k = _
    ring
  simp_rw [ke]
  rw [← Finset.mul_sum,Port.harvestQ]

end YM.Integration.WilsonLongContactStock
