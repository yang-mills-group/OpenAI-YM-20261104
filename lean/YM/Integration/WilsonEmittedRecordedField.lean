import YM.Integration.WilsonEmittedGroupWallet
import YM.QuadraticLocal.Class.Foundry

/-! Restoring the common Laurent shift on the true numerical group field
returns precisely the fired coefficient from the original uncut sum. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonEmittedRecordedField
open Function Finset Lattice Wilson RG Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise
open WilsonEmittedCutGrouping
open scoped BigOperators Classical
variable {G : Gauge} {n : Side} {V X ι : Type} [DecidableEq V]
variable {P : Passport n V} {Γ : Census V} (M : ι → Row P Γ G X)
variable (x : X) (w : V → ℕ) {σ : ℝ} {p : ℕ}
variable (staff : Air.Staff M (fun i=>(M i).paint x) w σ p)
variable (s : Γ.Mode) {g : ℝ} (live : g≠0)
local notation "q" => (fun i : ι=>(M i).paint x)
local notation "a" => (Launch.index Γ w s+1)
local notation "δ" => (((g^a:ℝ):ℂ))⁻¹

include staff live in
theorem value (μ : ι→Prop) (fit : ∀i,μ i→picked M s i) (U : Config G n) :
    (∑' i : ι, if μ i then (M i).nominal g x U else 0) =
      δ * Air.sums M q μ g U := by
  rw [Air.sums,←tsum_mul_left]
  apply tsum_congr
  intro i
  by_cases hi : μ i
  · simp only [if_pos hi]
    have eqn : (M i).lamp.power=a := congrArg (·+1) ((staff.written i).trans (congrArg (Launch.index Γ w) (fit i hi).symm))
    have re:=Sunrise.Loan.emission (M i).lamp (M i).atom (M i).center g live U
    change (M i).paint x * ↑(g^(M i).lamp.lag*(M i).atom.unmasked U (M i).center)=_
    rw [←re,eqn]
    simp only [ScatterR.familyAt,Complex.ofReal_mul,Complex.ofReal_inv]
    ring
  · simp [hi]

include staff live in
theorem uncut (U : Config G n) (posted : Summable (fun i=>Spill.raw M g x i U)) :
    (Spill.Foundry.uncut M g x U).part s = δ * Air.sums M q (picked M s) g U := by
  let h:=((Pi.hasSum.mp posted.hasSum) s).tsum_eq.symm
  apply h.trans
  change (∑' i : ι, (Poly.send (M i).mode ((M i).nominal g x U)).part s)=_
  rw [←value M x w staff s live (picked M s) (fun _ h=>h) U]
  apply tsum_congr
  intro i
  by_cases hi : s=(M i).mode <;> simp [Poly.part_send,picked,hi]

end YM.Integration.WilsonEmittedRecordedField
end
