import YM.Integration.WilsonIndependentFittedRelativeClock

/-! The occupied ordinary product carries a thermal scalar in either slot,
with the original angular symmetrization and thermal coefficient convention. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentFittedThermalProduct
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Finset Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open scoped BigOperators Topology Classical
variable {Z:Type*}

private theorem webbed {i j:ℕ}{ι:Type*}(s:Finset ι)(c:ι→ℝ)(P:ι→Ten ℝ Z i)(Q:Ten ℝ Z j)(r:ℕ):
    webT (∑a∈s,c a • P a) Q r=∑a∈s,c a • webT (P a) Q r ∧
    webT Q (∑a∈s,c a • P a) r=∑a∈s,c a • webT Q (P a) r:=by
  constructor <;> funext x <;> unfold webT <;> split
  · simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_mul,mul_assoc]
  · simp
  · simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
    exact sum_congr rfl (fun _ _=>by ring)
  · simp

private theorem turn {r:ℕ}(a:ℝ)(P:Ten ℝ Z r):swirl (a • P)=a • swirl P:=by
  funext x
  simp only [swirl,Pi.smul_apply,Finset.sum_apply,smul_eq_mul,Finset.mul_sum]
  exact sum_congr rfl (fun _ _=>by ring)

private theorem knitted {ι:Type*}(s:Finset ι)(c:ι→ℝ)(P:ι→Gen ℝ Z)(Q:Gen ℝ Z):
    knitS (∑a∈s,c a • P a) Q=∑a∈s,c a • knitS (P a) Q ∧
    knitS Q (∑a∈s,c a • P a)=∑a∈s,c a • knitS Q (P a):=by
  constructor <;> funext r
  · simp only [knitS,Finset.sum_apply,Pi.smul_apply,(webbed ..).1]
    rw [Finset.sum_comm]
    simp only [←Finset.smul_sum,swirl_sum,turn]
  · simp only [knitS,Finset.sum_apply,Pi.smul_apply,(webbed ..).2]
    rw [Finset.sum_comm]
    simp only [←Finset.smul_sum,swirl_sum,turn]

theorem left (c:Cost)(P Q:Pal ℝ Z):woad (affix c P) Q=affix c (woad P Q):=by
  funext n
  simp only [woad,affix,(knitted ..).1,Finset.smul_sum]
  exact triangle (fun a b d=>coeff a c • knitS (P b) (Q d)) n

theorem right (c:Cost)(P Q:Pal ℝ Z):woad P (affix c Q)=affix c (woad P Q):=by
  funext n
  simp only [woad,affix,(knitted ..).2,Finset.smul_sum]
  let F:=fun a b d=>coeff a c • knitS (P b) (Q d)
  let run:=fun (t:ℕ×ℕ)=>∑j∈antidiagonal t.2,F j.1 t.1 j.2
  change (∑t∈antidiagonal n,run t)=∑t∈antidiagonal n,∑j∈antidiagonal t.2,F t.1 j.1 j.2
  rw [←triangle F n]
  calc
    _ = ∑t∈antidiagonal n,∑j∈antidiagonal t.1,F j.2 j.1 t.2 := (triangle (fun a b d=>F b a d) n).symm
    _ = ∑t∈antidiagonal n,∑j∈antidiagonal t.1,F j.1 j.2 t.2 := by
      apply sum_congr rfl
      intro t _
      exact Finset.Nat.sum_antidiagonal_swap (n:=t.1) (f:=fun j:ℕ×ℕ=>F j.1 j.2 t.2)

end YM.Integration.WilsonIndependentFittedThermalProduct
