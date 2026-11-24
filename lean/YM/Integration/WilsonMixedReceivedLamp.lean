import YM.Integration.WilsonMixedReceivedInventory

/-! The canonical old regular and analytic addresses on a joint old and born passport. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMixedReceivedLamp
open Finset Function Lattice Wilson RG Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Affinity
open Push Push.AbsoluteSums Next.Foundations
open WilsonMixedTestTableau WilsonMixedPassportRows
open private transport from YM.Integration.WilsonMixedTestTableau
open scoped BigOperators Classical

variable {G : Gauge} {n : Side} {V I : Type} [DecidableEq V] [Fintype V] {J : Census V}
  {P Q : Passport n V} {W : Rep G n} {E F : V → Type}
  [∀ v, AddCommGroup (E v)] [∀ v, AddCommGroup (F v)] [∀ v, Module ℝ (E v)] [∀ v, Module ℝ (F v)]
  (A : ∀ v, Set (E v)) (B : ∀ v, Set (F v))
  (K : ∀ v, Submodule ℝ (E v)) (L : ∀ v, Submodule ℝ (F v))
  (old : Finset V) (zeroA : ∀ v, 0 ∈ A v)
  (L₀ : Lamps (Wallet A) I G W.p P.origin J)
local notation "test" => left A B old zeroA
local notation "joined" => passport (owner P Q old)

def regular : Lamps (Wallet (actors A B)) ({i : I // (L₀.mode i).val ⊆ old}) G W.p (joined).origin J where
  mode i := L₀.mode i.val
  live i := L₀.live i.val
  address i := L₀.address i.val
  roots i v hv := by
    change (owner P Q old v).origin v ∈ _
    rw [show owner P Q old v = P from if_pos (i.property hv)]
    exact L₀.roots i.val v hv
  nominal t i := L₀.nominal (test t) i.val
  legal t i := L₀.legal (test t) i.val
  clear i := L₀.clear i.val
  pure t i := L₀.pure (test t) i.val

local notation "rows" => regular (Q:=Q) A B old zeroA L₀

omit [Fintype V] [∀ v, Module ℝ (E v)] [∀ v, AddCommGroup (F v)] [∀ v, Module ℝ (F v)] in
theorem paid {w w' : V → ℝ} (positive' : ∀ v, 0 < w' v)
    (fits : ∀ v ∈ old, w' v ≤ w v) {d : ℕ} {a c : ℝ} (reg : L₀.Paid w d a c) :
    (rows).Paid w' d a c := by
  obtain ⟨f, pos, valid, hit⟩ := reg.budget
  refine ⟨fun i => f i.val, fun i => pos i.val, fun i t => valid i.val (test t), ?_⟩
  intro x
  apply budget_mono (budget_pull (Subtype.val : {i : I // (L₀.mode i).val ⊆ old} → I) Subtype.val_injective (hit x))
  · intro i
    change 0 ≤ if x ∈ L₀.ground i.val then Poly.toll w' (L₀.mode i.val)*f i.val*
      Real.exp (a*coverNumber d (L₀.ground i.val)) else 0
    split
    · positivity [Poly.worth positive' (L₀.mode i.val), pos i.val]
    · exact le_rfl
  · intro i
    change (if x ∈ L₀.ground i.val then Poly.toll w' (L₀.mode i.val)*f i.val*_
      else 0) ≤ (if x ∈ L₀.ground i.val then Poly.toll w (L₀.mode i.val)*f i.val*_ else 0)
    split
    · exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (Finset.prod_le_prod (fun v _ => (positive' v).le)
          (fun v hv => fits v (i.property hv))) (pos i.val)) (Real.exp_pos _).le
    · exact le_rfl

variable (H : Hard (Wallet A) W.p W.activities.forced W.activities.K P.origin J)
  (hc:Crown P.support A K H) (hf:Taut P.support A K L₀)

include H hc hf
omit [Fintype V] in
theorem heard {w : V → ℝ} (positive : ∀ v,0<w v) {d : ℕ} {a c : ℝ} (enabled:0≤a)
    (fee:L₀.Paid w d a c) :
    Taut (joined).support (actors A B) (pieces K L) (rows) ∧
    ∀ t U,(rows).log t U=L₀.log (test t) U := by
  let intake : Tint.Incoming P W (Wallet A) I J := ⟨L₀,H⟩
  refine ⟨WilsonMixedReceivedInventory.taut (Q:=Q) A B K L old zeroA intake hf,?_⟩
  exact fun t U=>(WilsonMixedReceivedInventory.physical (Q:=Q) A B K old zeroA intake hf hc
    positive enabled fee t U).1

end YM.Integration.WilsonMixedReceivedLamp
