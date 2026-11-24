import YM.RG05Readout.Many.Release

/-! Reopen the represented restricted source on the full physical ward at
the same small price, before its mixed coefficients are tagged. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMixedTaggedReopening
open Finset Function Set Lattice Wilson RG Marker RG05Readout Many MergeProof Accent Extra.Histories
open scoped BigOperators Classical

theorem original {G:Gauge} {n:Side} {V:Type} [DecidableEq V] [Fintype V] {B C:Census V}
    (inc:B.choices⊆C.choices) (D:Set V) {R:Rep G n}
    {Φ:V → Config G n → ℂ} {κ:V → Box n → Config G n → ℂ}
    {o:V → Site n} {w:V → ℝ} {α δ:ℝ} {X:Config G n → Poly C}
    (dormant:∀i∈D,Φ i=0 ∧ κ i=0) (wp:∀v,0 < w v)
    (gate:∀i:C.Mode,i.val∉B.choices → ¬Disjoint D (i.val:Set V))
    (dark:∀U i,¬Disjoint D (i.val:Set V) → (X U).part i=0)
    (small:Served R Φ κ (fun U=>narrow inc (X U)) o w α δ) :
    Served R Φ κ X o w α δ := by
  let z U:=temperV B D (narrow inc (X U))
  have restricted:Served R Φ κ z o w α δ:=temper_served D dormant wp small
  have off U (i:B.Mode) (crossed:¬Disjoint D (i.val:Set V)) : (z U).part i=0 := by
    simp only [z,temper_part,if_neg crossed]
  have reopened:=open_served inc D dormant wp restricted off gate
  have eq:(fun U=>wrap B C (z U))=X := by
    funext U
    ext i
    by_cases hi:i.val∈B.choices
    · let j:B.Mode:=⟨i.val,hi⟩
      rw [show i=route inc j from rfl,wrap_right]
      dsimp only [z]
      rw [temper_part,narrow_right]
      split_ifs with lit
      · rfl
      exact (dark U _ lit).symm
    rw [wrap_off _ _ hi,dark U _ (gate i hi)]
  exact eq ▸ reopened

end YM.Integration.WilsonMixedTaggedReopening
