import YM.Integration.WilsonOriginalAlternativeRetestedIncome
import YM.QuadraticLocal.Germ.Harper

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeSelectedInventory
open Function Finset Set Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Affinity
open WilsonOriginalAlternativeNames WilsonOriginalAlternativeRetest
open scoped Classical BigOperators
variable {V:Type} [DecidableEq V] {X:V→Type} [∀i,AddCommGroup (X i)] [∀i,Module ℝ (X i)]
  (A:∀i,Set (X i)) (K:∀i,Submodule ℝ (X i)) (zero:∀i,0∈A i) (c:V→Port)
variable {G:Gauge} {n:Side} {J:Census V} {I E M:Type} {W:Rep G n} {P:Passport n V}
  (Z:Tint.Incoming P W (Wallet A) I J) (L:Lamps (Wallet A) E G W.p P.origin J)
local notation "test_" => submitted A zero c
def joined:Tint.Incoming P W (Wallet A) (I⊕E) J:=
  ⟨(Z.old.pullback test_).join L,Z.hard.pullback test_⟩

omit [∀i,Module ℝ (X i)] in
theorem paid {w:V→ℝ} {b:ℕ} {a r e κ:ℝ} (old:Z.old.Paid w b (a+1+1) r)
    (hard:Z.hard.Paid w b a κ) (added:L.Paid w b (a+1+1) e):
    let Y:=joined A zero c Z L
    Y.old.Paid w b (a+1+1) (r+e) ∧ Y.hard.Paid w b a κ:=
  ⟨Lamps.joinPaid (WilsonOriginalAlternativeRetestedIncome.regular A zero c _ old) added,
    WilsonOriginalAlternativeRetestedIncome.hard A zero c _ hard⟩

theorem registered (old:Taut P.support A K Z.old) (hard:Crown P.support A K Z.hard)
    (added:Taut P.support A K L):
    let Y:=joined A zero c Z L
    Taut P.support A K Y.old ∧ Crown P.support A K Y.hard :=
  ⟨Polish.Static.spawn (WilsonOriginalAlternativeRetestedIncome.old A K zero c P.support Z.old old) added,
    WilsonOriginalAlternativeRetestedIncome.owner A K zero c P.support Z.hard hard⟩

end YM.Integration.WilsonOriginalAlternativeSelectedInventory
