import YM.Integration.FundedPeriodAction
import YM.Integration.ActualGradedVacuum
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Song.Procession

/-! Construct the original physical packet encoding of a signed finite
torus correction, including every oriented atom and its actual root. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FundedPeriodPayload
open Function Filter Finset Lattice Laurent Bloch Wilson RG Precision Exterior Tree
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open FreeResolvent PhysicalNext.Repeat PhysicalNext.Repeat.Song Extra.Iteration
open IterationFour IterationFour.Vacuum LocalComparison.Global FullQLocal
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {s A : ℝ} (n : Side)

def addressBook : ℕ ≃ Stave (n:=n) := numbering _

def payload (a : PrismA G) : Payload G n where
  labels i := Song.pitch a.cells (addressBook n i)
  action i := Song.tuneAtom a.cells 1 (addressBook n i)

def piece (credit : ℝ) (a : PrismA G) : Piece G n where
  power := a.grade
  rank := a.rise+2
  packet := payload n a
  credit := credit

theorem masked (hs : 0 < s) (a : PrismA G) (ha : Commission a.cells s A a.grade)
    (p : BudgetPoint) (U : Config G n) :
    (payload n a).amount p U = Song.billOf p a.cells U := by
  let f := fun i : Song.Stave (n:=n) => RG.masked p.threshold (Song.pitch a.cells i).support
    (Song.tuneAtom a.cells 1 i) U
  calc
    _ = ∑' i : ℕ, f (addressBook n i) := rfl
    _ = ∑' i : Song.Stave (n:=n), f i := (addressBook n).tsum_eq f
    _ = _ := by simpa only [one_mul] using (Song.allocated p a.cells U 1 hs ha.toll).tsum_eq

private lemma turn (a : PrismA G) (i : Signed × Site n) (j : ℕ) (U : Config G n) :
    (a.cells j).unmasked ((Song.splay n i).view U) 0 =
      (a.cells j).unmasked (pull i.1 0 U) i.2 := by
  have he : (Song.splay n i).view U = translate i.2 (pull i.1 0 U) := by
    rw [← Lattice.pull_one,Lattice.pull_pull,mul_one,affine,add_zero]
    rfl
  have hz : expandAt (0 : Site n) (translate i.2 (pull i.1 0 U)) = expandAt i.2 (pull i.1 0 U) := by
    rw [← Lattice.pull_one,expandAt_pull]
    simp [affine]
  unfold Atom.unmasked Slot.atSite
  rw [he,hz]

theorem unmasked (hs : 0 < s) (a : PrismA G) (ha : Commission a.cells s A a.grade)
    (U : Config G n) :
    unmaskedPayload (payload n a) U = FundedPeriodAction.action n a U := by
  let c : ℝ := (Fintype.card Signed : ℝ)⁻¹
  let f (i : Stave (n:=n)) := Song.tuneAtom a.cells 1 i U
  have hf (i : Stave (n:=n)) : f i = c * (a.cells i.2).unmasked (i.1.view U) 0 := by
    change (c*1)*_ = _
    rw [mul_one]
  let view (i : Signed × Site n) := ((i,0) : Stave (n:=n)).1.view U
  have hs' (i : Signed × Site n) : Summable (fun j => (a.cells j).unmasked (view i) 0) :=
    NativeBoundedAtomSeries.value_summable a.cells (fun _ => (0:Site n)) hs
      (fun _ => le_rfl) ha.toll.2.1 (view i)
  have hv (i : Signed × Site n) : HasSum (fun j => f (i,j))
      (c * ∑' j, (a.cells j).unmasked (view i) 0) := by
    simp_rw [hf]
    exact (hs' i).hasSum.mul_left c
  have h := ConnectedActivityE6.Raw.finite_start f _ hv
  calc
    _ = ∑' j : ℕ, f (addressBook n j) := rfl
    _ = ∑' i : Stave (n:=n), f i := (addressBook n).tsum_eq f
    _ = ∑ i : Signed × Site n, c * ∑' j, (a.cells j).unmasked (view i) 0 := h.tsum_eq
    _ = _ := by
      rw [← Finset.mul_sum,← Equiv.sum_comp (Song.splay n) (fun i => ∑' j,(a.cells j).unmasked (view i) 0),
        Fintype.sum_prod_type]
      dsimp only [view]
      simp_rw [turn n a _ _ U]
      rfl

theorem restored (hs : 0 < s) (Z : SeriesA G) (hZ : Draw Z s A) (g : ℝ) (U : Config G n) :
    ActualGradedVacuum.restored (Z.map (piece n A)) g U = FundedPeriodAction.rendered n Z g U := by
  induction Z with
  | nil => rfl
  | cons a Z ih =>
    have hd : a.grade+2-(a.rise+2) = a.grade-a.rise := by omega
    change g^(a.grade+2-(a.rise+2)) * unmaskedPayload (payload n a) U +
      ActualGradedVacuum.restored (Z.map (piece n A)) g U =
      g^(a.grade-a.rise) * FundedPeriodAction.action n a U + FundedPeriodAction.rendered n Z g U
    rw [hd,unmasked n hs a (hZ.2 a List.mem_cons_self) U,
      ih ⟨hZ.1,fun b hb => hZ.2 b (List.mem_cons_of_mem a hb)⟩]

end YM.Integration.FundedPeriodPayload
