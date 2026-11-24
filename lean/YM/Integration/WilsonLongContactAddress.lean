import YM.Integration.WilsonCloseCapturePositions
import YM.LocalLTE.Port.Shift

/-! Filed regular coefficients carried by one original occupied mode, with the older gas retained. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonLongContactAddress
open Lattice Wilson RG Source Marker PhysicalNext.Repeat PhysicalNext.Repeat.Lotus
open LocalLTE WilsonLimitConstruction MeasureTheory MergeProof PhysicalNext.Repeat.Legato Progress.DirectedRecipe
open scoped Classical BigOperators
variable {G : Gauge} {n : Side}

theorem available (R : Run G) (simple : G.Simple) (N per j : ℕ) (hj : j ≤ N) :
    HasSlots (R.family.path.rep N per j).p (R.family.path.rep N per j).activities :=
  Vintage.YM.PhysicalNext.Repeat.Graces.Nest.samples simple
    (WilsonCloseCapturePositions.nested R) N j per hj

theorem density {Q : Rep G n} (L : Leaf Q) (i : ℕ) (key : L.turn = .logKey i)
    (U : Config G n) : L.cicada U = L.ingredient U * Q.eval U := by
  have hb (k : Finset ℕ) : L.bun k U = L.ingredient U * Q.activities.gasOccurrence Q.p k U := by
    unfold Leaf.bun Leaf.bill Activities.gasOccurrence
    rw [key]
    by_cases ha : Q.activities.admissible Q.p U k <;>
      simp [ha, Wing.Occupied, Wing.remaining]
  unfold Leaf.cicada Rep.eval Activities.gas
  simp_rw [hb]
  rw [tsum_mul_left]
  ring

variable {V : Type} [DecidableEq V]

/-- The complete declared subset is retained at one regular activity address and every old
admissible hard roster is still present in its physical density. -/
theorem filed (A : Run G) (simple : G.Simple) (N per j : ℕ) (hj : j ≤ N)
    (z : Site (A.family.S.side j per)) (J : Census V) (s : J.Mode) (hs : s.val.Nonempty)
    (X : RegularAddress (A.family.S.side j per)) (copy : ℕ)
    (f : Config G (A.family.S.side j per) → ℂ) (w : ℝ)
    (regular : (A.family.path.rep N per j).p.Regular X.support f)
    (paid : (A.family.path.rep N per j).p.supBounds z X.support f w) (part : Bool) :
    let Q := A.family.path.rep N per j
    let h := fun U => Port.scaleQ part (masked Q.p.threshold X.support f U)
    ∃ L : Menu.Hat J Q, L.s = s ∧ L.M.turn = .logKey (blankRow _ (X,copy)) ∧
      L.M.crest = X.support ∧ L.M.weight = w ∧ L.M.ingredient = h ∧
      (∀ U, Menu.amount L U = Poly.send s ((h U : ℂ) * Port.ink part)) ∧
      ∀ U, L.M.cicada U = h U * Q.eval U := by
  intro Q h
  obtain ⟨hr,hp⟩ := Port.framesV regular paid part
  let f' := Port.scaleQ part ∘ f
  let h' := masked Q.p.threshold X.support f'
  have he : h' = h := funext fun U => Port.stratum U part _ f
  have sale := Port.supportQ Q.p z hr hp
  have slots := available A simple N per j hj
  let L := Port.salesZ Q J X copy h' s hs w (Port.ink part) sale slots
  obtain ⟨key,crest,⟨_,val,weight⟩,mode,_,amount⟩ :=
    Port.birthZ Q J X copy h' s hs w part (fun _ => 1) sale slots
  have hi : L.M.ingredient = h := he
  exact ⟨L,mode,key,crest,weight.trans val,hi,he ▸ amount,
    fun U => (density L.M _ key U).trans (by rw [hi])⟩

end YM.Integration.WilsonLongContactAddress
