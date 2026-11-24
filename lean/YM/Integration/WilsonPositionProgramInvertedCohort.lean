import YM.Integration.WilsonPositionProgramInversionAlgebra
import YM.Integration.WilsonPositionProgramInvertedWords
import YM.Integration.WilsonPositionProgramLocatedFieldCourse

/-! The genuine normalized top of the independent master, with a real child
in each slot, is a single full polynomial on the actual inversion tree. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
namespace YM.Integration.WilsonPositionProgramInvertedCohort
open Set Function Filter Finset Matrix PowerSeries Lattice Wilson RG PhysicalNext.Repeat.Legato
open Precision XSpace Labels Source PertExtension.Orb
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Soil WilsonCoeffUV.Power
open WilsonCoeffUV.Shard WilsonCoeffUV.Embroider WilsonCoeffUV.Blue
open WilsonPositionProgramInversionAlgebra WilsonPositionProgramInvertedStencil
open WilsonPositionProgramInversionMaterial
open scoped Classical BigOperators Topology
variable {G : Gauge} (R : Run G) {p : Period} (T : p.Tree) {I : Type} [Fintype I] [LinearOrder I]
    (d h : I → ℕ) (fit : ∀ j,d j < h j) (z : I → Cover)
local notation "F" j => R.family.labels.level (d j)
local notation "rank" j => WilsonPositionProgramMasterBirth.rank R (d:=d j)

omit [LinearOrder I] in
theorem pay (w : (j : I) → Verse (F j)) (b : (j : I) → Volume (h j)) (a : Axes R d) :
    (∏ j, income (G:=G) T (X^((rank j)-valence (F j) (a j)) *
        (PowerSeries.map (algebraMap ℝ ℂ) (w j (a j)) * C ((jewelBloom (fit j) (a j) (b j):ℝ):ℂ)))) =
      income T (X^(ceiling R d-degree R d a)*dose R d w h fit b a) := by
  let α := fun j => (rank j)-valence (F j) (a j)
  have add : (∑ j,α j)+degree R d a=ceiling R d := by
    change (∑ j,α j)+(∑ j,valence (F j) (a j))=∑j,(rank j)
    rw [←Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => Nat.sub_add_cancel (Finset.le_sup (f:=valence (F j)) (mem_univ _))
  have sub : (∑ j,α j)=ceiling R d-degree R d a := by omega
  rw [←map_prod,Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]
  change income (G:=G) T (X^(∑ j,α j)*dose R d w h fit b a)=_
  rw [sub]

theorem assembled (w : (j : I) → Verse (F j)) (b : (j : I) → Volume (h j))
    (running : I → Ink (Woods G p.side))
    (issued : ∀ j, (X:Ink (Woods G p.side))^(rank j) * running j =
      loom (spear (jog (wrap p.side (z j)) : Woods G p.side ≃ Woods G p.side))
        (∑ s, X^((rank j)-valence (F j) s)*soil (w j s)*
          (jewelBloom (fit j) s (b j) • jet (Plies (R.family.localSection (d j)) (sheet (F j) s) p.side)))) :
    packet T (X^ceiling R d * ∏ j,running j) =
      finite R p d z T (dose R d w h fit b) := by
  have one j : packet T (X^(rank j)*running j) = ∑ s : Alma (F j),
      (income T (X^((rank j)-valence (F j) s) *
        (PowerSeries.map (algebraMap ℝ ℂ) (w j s)*C ((jewelBloom (fit j) s (b j):ℝ):ℂ)))) *
          Taylor.expandTaylor (T.basis G) (Complex.ofRealCLM ∘
            (SlotEvaluation.fieldAt (R.family.localSection (d j)) (sheet (F j) s)
              (wrap p.side (z j)) ∘ T.links)) := by
    rw [issued j,map_sum,map_sum]
    apply Finset.sum_congr rfl
    intro s _
    rw [WilsonPositionProgramInversionAlgebra.term,WilsonPositionProgramInvertedStencil.original]
  have group : (X:Ink (Woods G p.side))^ceiling R d * ∏ j,running j =
      ∏ j, X^(rank j)*running j := by rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum];rfl
  rw [group,map_prod]
  simp_rw [one]
  rw [Finset.prod_univ_sum,finite]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.prod_mul_distrib,pay R T d h fit]
  exact congrArg (fun v=> Bare.scalar T (X^(ceiling R d-degree R d a)*dose R d w h fit b a)*v)
    (WilsonPositionProgramInvertedWords.original T R d z a).symm

end YM.Integration.WilsonPositionProgramInvertedCohort
end
