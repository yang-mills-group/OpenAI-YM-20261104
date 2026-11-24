import YM.Integration.WilsonPointChildFiniteSeam
import YM.Integration.WilsonPointChildPairedHistory
import YM.Integration.WilsonPointChildWidthPortfolio
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPointChildFiniteRestamp
open Function Filter Finset Matrix Lattice Wilson RG Laurent PowerSeries Work.F08
open FormalBulk08 Flat Reef Jets Orb Wick Stationary Series Shore Gorge Lotus Mesa Rift Lava Dawn Kemp Roof Sierra Rial
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Power
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Winding
open YM Next.Foundations PhysicalNext.Repeat.Legato Pose Palm Quire Wine Dove WilsonCoeffUV.Embroider
open WilsonPointChildTestCoordinates WilsonNeutralPointCourse WilsonPointChildCoverStep
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped Classical Topology BigOperators ContDiff
open YM FormalBulk08 Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof Quire Dove Dove.Lab Sierra
open PhysicalNext.Repeat.Legato Next.Foundations Borough
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open WilsonPointChildNormalizedWidth WilsonNeutralPointCourse WilsonPointChildFiledPress WilsonPointChildFiledSalary
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
open WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Mer
open WilsonPointChildEra (funded)
variable {G:Gauge}

def difference (X:Era G ℝ)(n:Side)(e r:ℕ)(x:Fin r → Woods G n):ℝ:=X.1 n e r x-plume (X.2 e r) n x

private theorem sums {α:Type}(J:Finset α){r:ℕ}(F:α → Ten ℝ (YForest G) r)(n:Side)
    (funding:∀t∈J,∃s C:ℝ,0<s ∧ Cork terrain 0 s C (F t)):
    plume (∑t∈J,F t) n=∑t∈J,plume (F t) n:=by
  funext x
  have point y:peglet (∑t∈J,F t) n x y=∑t∈J,peglet (F t) n x y:=by
    by_cases h:slideC n y=x <;>simp [peglet,h,Finset.sum_apply]
  change (∑' y,peglet (∑t∈J,F t) n x y)=_
  simp_rw [point]
  rw [Summable.tsum_finsetSum]
  · rw [Finset.sum_apply];rfl
  · intro t ht;obtain ⟨s,C,ss,W⟩:=funding t ht;exact creased W ss n x

private theorem scalar {α:Type}{r:ℕ}(q:ℝ)(T:Ten ℝ (Cloth α) r)(n:Side)(x):
    plume (q•T) n x=q*plume T n x:=by
  have point y:peglet (q•T) n x y=q*peglet T n x y:=by
    by_cases h:slideC n y=x <;>simp [peglet,h]
  change (∑' y,peglet (q•T) n x y)=_
  simp_rw [point]
  exact tsum_mul_left

theorem total {d:ℕ}{α:Type}(J:Finset α)(F:α → Era G ℝ)(legal:∀t∈J,Auth d (F t))(n:Side)(e r:ℕ)(x):
    difference (∑t∈J,F t) n e r x=∑t∈J,difference (F t) n e r x:=by
  simp only [difference,Prod.fst_sum,Prod.snd_sum,Finset.sum_apply]
  rw [sums J _ n (fun t ht=>((legal t ht).wing e r).land),Finset.sum_apply,Finset.sum_sub_distrib]

theorem scored {d:ℕ}(q:Cost)(μ:ℝ)(X:Era G ℝ)(authorized:Auth d X)(n:Side)(e r:ℕ)(x):
    difference (funded q (μ•X)) n e r x=
      ∑z∈Finset.HasAntidiagonal.antidiagonal e,coeff z.1 q*(μ*difference X n z.2 r x):=by
  let term (z:ℕ×ℕ):=coeff z.1 q • (μ • X.2 z.2 r)
  have receipt z:(∃s C:ℝ,0<s ∧ Cork terrain 0 s C (term z)):=by
    exact ((((authorized.μ μ).μ (coeff z.1 q)).wing z.2 r).land)
  change (affix q (μ•X.1 n)) e r x-plume ((affix q (μ•X.2)) e r) n x=_
  simp only [affix,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  rw [sums (G:=G) (Finset.HasAntidiagonal.antidiagonal e) term n (fun z _=>receipt z),Finset.sum_apply,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro z _
  simp only [term,scalar,difference];ring

theorem original {d:ℕ}(F:Frame G d)(M:Tilework F)(p:Letter F)(X:Letter F → Era G ℝ)
    (auth:∀s,Auth d (X s))(n:Side)(e r:ℕ)(x)(μ B:ℝ)
    (incoming:∀s,∀b ≤ e,|difference (X s) n b r x| ≤ B):
    |difference (∑s,funded (M s p) (μ•X s)) n e r x| ≤ inverseCost F M p e*(|μ| * B):=by
  rw [total _ _ (fun s _=>WilsonPointChildEra.checked ((auth s).μ μ) _) n e r x]
  simp_rw [scored _ _ _ (auth _) n e r x]
  apply (Finset.abs_sum_le_sum_abs ..).trans
  unfold inverseCost
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro s _
  rw [Finset.sum_mul]
  apply (Finset.abs_sum_le_sum_abs ..).trans
  apply Finset.sum_le_sum
  intro z hz
  have le:z.2 ≤ e:=by have:=Finset.HasAntidiagonal.mem_antidiagonal.mp hz;omega
  rw [abs_mul,abs_mul]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (incoming s _ le) (abs_nonneg _)) (abs_nonneg _)

end YM.Integration.WilsonPointChildFiniteRestamp
