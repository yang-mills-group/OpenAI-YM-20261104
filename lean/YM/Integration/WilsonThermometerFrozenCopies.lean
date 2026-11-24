import YM.Integration.WilsonThermometerFrozenSockets
import YM.Integration.FVA1Physical.TwoReset.CopyLetters

/-! Finite and repeated copies of the fixed, inverse-fitted physical numbers
at the literal three placements retain their independent Wilson path sockets. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerFrozenCopies
open Finset Function Lattice Wilson RG Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise
open Comparison.RG02.Bulk Next.SectorChange Multi AllOrder AllOrder.Floe
open Further.PhysicalPeriodLimitF933 Macrame Shingle
open PhysicalNext.Repeat.Legato ActualRunCurvaturePackets NativeCurvatureTensor
open WilsonOriginalStarSceneWords WilsonOriginalStarGradedScene
open FVA1Physical.TwoReset WilsonThermometerFrozenSockets
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) {V T : Type} [DecidableEq V] [Fintype V]
  (d : V→ℕ) {n f : Side} (o : V→Site n) (σ g τ : ℝ)
  (v : (j:V)→R.family.label (d j)) (t : V→T→ℂ) (pos : ∀j, 0<d j)
local notation "M" => words R d o σ g τ v t pos

def word (i : Entry R d) (s : ℝ) (x : T) (z : Site f) (U : Config G f) : ℂ :=
  (t (root R d i) x*scalar R d 1 1 v i)*
  (((g/τ)^(pole R d i)*s^(d (root R d i)+1-pole R d i):ℝ):ℂ) *
  ↑((raw R d i).unmasked U z)

theorem repeated (h : n.val∣f.val) (i : Entry R d) (s : ℝ) (x : T) (U : Config G f) :
    (M i).paint x * copiesLetter h M i s U =
      ∑ z∈parcel (splitter h) (M i).center, word R d g τ v t i s x z U := by
  unfold copiesLetter
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  exact painted R d o σ g τ v t pos i s x z U

theorem colored (h : n.val∣f.val) (x : T) (L : Layout G) (pay : Finset Age)
    (s : Multi.Hot (Stock.census V)) (u : ℝ) (U : Config G f) :
    (copyColor h M d (fun j=>(M j).paint x) L pay).mark s u U =
      ∑ p : Fin (Pages n f), ∑ j : Entry R d,
        if (ScatterR.actor (fun a=>FVA1Physical.TwoReset.copy h (M a) p) j).val = s.val then
          word R d g τ v t j u x (FVA1Physical.TwoReset.copy h (M j) p).center U else 0 := by
  classical
  unfold copyColor
  simp only [Finset.sum_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [Air.craft,QuadraticLocal.Fk.grant,Air.sums]
  rw [tsum_fintype]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs
  · exact painted R d o σ g τ v t pos j u x (FVA1Physical.TwoReset.copy h (M j) p).center U
  · rfl

end YM.Integration.WilsonThermometerFrozenCopies
