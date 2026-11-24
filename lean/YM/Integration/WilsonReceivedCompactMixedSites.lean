import YM.Integration.WilsonCapturedPrimaryCaptureRoom
import YM.Integration.WilsonReceivedCompactQSampling

/-! Both marked birth clocks enter the same original geometric capture. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section

namespace YM.Integration.WilsonReceivedCompactMixedSites
open Lattice Wilson RG Extraction Cells RG12 Filter MeasureTheory Set XSpace
open PhysicalNext.Repeat.Legato Finset WilsonReceivedCompactPriorIntegral
open WilsonReceivedCloseCompactStations
open scoped Classical BigOperators Topology

variable {G : Gauge} (R : Run G)

local notation "Sites" d:max p:max => Fin 3 → Site (R.family.side d p)
local notation "Bins" b:max p:max => (Sites ((b+1)+1) p) × (Sites (b+1) p)

def roots {i b : ℕ} (ib:i ≤ b) (per:ℕ) (old:Finset (Fin 3)) (o:Bins b per) (v:Fin 3) :
    Site (R.family.side i per) :=
  if v∈old then
    (R.family.S.toDepth (ib.trans ((Nat.le_succ b).trans (Nat.le_succ (b+1)))) per).parent (o.1 v)
  else (R.family.S.toDepth (ib.trans (Nat.le_succ b)) per).parent (o.2 v)

theorem active (test:Test 3) (r:ℝ) (b per:ℕ) (o:Bins b per)
    (charged:WilsonSeparatedOriginalThermometerCells.weight test (cells R b per r) o≠0) :
    ∃x:Points 3, test x≠0 ∧ cells R b per r x=o := by
  classical
  by_contra none
  let χ:=cells R b per r
  have zero (x:Points 3):(χ ⁻¹' {o}).indicator (fun z=>test z) x=0 := by
    by_cases hx:χ x=o
    · rw [Set.indicator_of_mem (show x∈χ ⁻¹' {o} from hx)]
      by_contra live
      exact none ⟨x,live,hx⟩
    · exact Set.indicator_of_notMem (show x∉χ ⁻¹' {o} from hx) (fun z=>test z)
  apply charged
  change (∫x:Points 3,(χ ⁻¹' {o}).indicator (fun z=>test z) x)=0
  simp_rw [zero]
  exact integral_zero _ _

/-- One cofinal cutoff for a compact shape, followed by every original volume and both birth meshes. -/
theorem original (simple:G.Simple) (test:Test 3) :
    ∀ᶠ i:ℕ in atTop, ∀ (b per:ℕ) (ib:i ≤ b) (r:ℝ), |r| ≤ R.family.S.a i →
    ∀ (old:Finset (Fin 3)) (o:Bins b per),
      WilsonSeparatedOriginalThermometerCells.weight test (cells R b per r) o≠0 →
      Nonempty (Housing (R.family.path.levels.budget i).B 0 (roots R ib per old o)) := by
  obtain ⟨K,bound⟩:=WilsonCapturedPrimaryCaptureRoom.shape test
  filter_upwards [(Multi.Wage.ranges simple R.family.path.levels).eventually_ge_atTop (K+2)] with i large
  intro b per ib r paid old o charged
  obtain ⟨x,live,site⟩:=active R test r b per o charged
  let B:=(R.family.path.levels.budget i).B
  have room (v:Fin 3) (a:Axis) : |(r • x) v a|+R.family.S.a i ≤ ((K+1:ℕ):ℝ)*R.family.S.a i := by
    change |r*x v a|+R.family.S.a i ≤ _
    rw [abs_mul,Nat.cast_succ,add_mul,one_mul]
    exact add_le_add ((mul_le_mul paid (bound x live v a) (abs_nonneg _) (R.family.S.a_pos i).le).trans_eq
      (mul_comm _ _)) le_rfl
  have cover {t:ℕ} (it:i ≤ t) (sites:Sites t per)
      (aligned:WilsonSeparatedOriginalThermometerCells.positions (R:=R) r (t,per) x=sites) (v:Fin 3):
      separation ((R.family.S.toDepth it per).parent (sites v)) 0 ≤ B := by
    rw [←aligned]
    exact (WilsonCapturedPrimaryCompactSites.ancestor R.family.S it (r • x) (K+1) room v).trans large
  have close (v:Fin 3) : separation (roots R ib per old o v) 0 ≤ B := by
    unfold roots
    split_ifs
    · exact cover _ o.1 (congrArg Prod.fst site) v
    · exact cover _ o.2 (congrArg Prod.snd site) v
  refine ⟨⟨halo B {0},?_,?_,B,close,le_rfl,fun _ h=>h⟩⟩
  · exact YM.Lattice.halo_subset B {0} (Finset.mem_singleton_self _)
  · intro v
    exact halo_spec.mpr ⟨0,mem_singleton_self _,by simpa only [separation_comm (0:Site _)] using close v⟩

end YM.Integration.WilsonReceivedCompactMixedSites
