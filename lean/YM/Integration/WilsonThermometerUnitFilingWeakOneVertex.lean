import YM.Integration.WilsonThermometerUnitFilingPinnedPole
import YM.Integration.WilsonFiniteMarkedWickDiagonal

/-! The actual earlier vacuum incident to one pinned ordinary insertion. At first positive thermal order a single quiet vertex enters the Gaussian recursion and its marked partner carries its full zeroth order. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingWeakOneVertex
open Filter Finset Function Lattice Laurent RG Precision Wilson Input WilsonCoeffUV
open WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Shard WilsonCoeffUV.Soil
open WilsonCoeffUV.Embroider WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open FreeResolvent AnalyticNext.QuarticMatch.Sheets Exterior Next.Free Tree Power Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm Fountain PathCost Embroider.Canvas Shard PowerSeries
open Org PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open scoped Classical BigOperators
variable {G:Gauge} {U W:Type} [Fintype U] [AddCommGroup W] [Module ℝ W]

private theorem absent (C:Matrix U U ℝ)(Q:Gen W U):arbor C (0:Gen ℝ U) Q=0:=by
  funext r
  exact arbor_zero_at C _ Q r (fun _ _ _=>Or.inl rfl)

theorem positive (C:Matrix U U ℝ)(V:Layers ℝ U)(Z:Layers W U)(gate:∀a,V a 0=0)(h e:ℕ):
    ravel C V Z h e=∑j∈antidiagonal h,∑k∈(antidiagonal e).filter (fun k=>k.2<e),arbor C (V j.1 k.1) (Z j.2 k.2):=by
  unfold ravel
  apply sum_congr rfl;intro j _
  symm;apply sum_subset (filter_subset _ _);intro k live idle
  have same:=mem_antidiagonal.mp live
  have no:¬ k.2<e:=fun klt=>idle (mem_filter.mpr ⟨live,klt⟩)
  have z:k.1=0:=by omega
  rw [z,gate,absent]

theorem grading (C:Matrix U U ℝ)(V:Layers ℝ U)(Z:ℕ→Gen W U)(gate:∀a,V a 0=0)(h:ℕ):
    (bul C V Z (h+1) 0=((h+1:ℕ):ℝ)⁻¹ • ripple C (bul C V Z h 0)) ∧
    bul C V Z (h+1) 1=((h+1:ℕ):ℝ)⁻¹ • (ripple C (bul C V Z h 1)+
       (∑j∈antidiagonal h,arbor C (V j.1 1) (bul C V Z j.2 0))+
       ∑j∈antidiagonal h,arbor C.transpose (V j.1 1) (bul C V Z j.2 0)):=by
  have zero (A:Matrix U U ℝ)(X:Layers W U):ravel A V X h 0=0:=by rw [positive A V X gate];simp
  have one (A:Matrix U U ℝ)(X:Layers W U):ravel A V X h 1=∑j∈antidiagonal h,arbor A (V j.1 1) (X j.2 0):=by
    rw [positive A V X gate]
    have singleton:(antidiagonal (1:ℕ)).filter (fun k=>k.2<1)={(1,0)}:=by decide
    rw [singleton];simp
  constructor
  · rw [bul_next,zero,zero,add_zero,add_zero]
  · rw [bul_next,one,one]

variable {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem original (R:Run G)(N i:ℕ)(n:Side)(w:Pal E (Woods G (n*(ll R.family.path.levels i).L))):
    let A:=R.family.path.levels
    let p:=ll A i
    let K:=A.clock.kernel
    let S:=stepAt p K n
    let F:=xree p K n
    let H:=freeForms A N (i+1)
    let Y:=roam A N i n
    let O:=R.metals.O
    let P:=(story A O N (i+1)).1 (n*p.L)
    let C:=fillSlots (Woods G n) (covariance G S F H)
    let V:=xray S F H Y O P
    let entry:=srShade S F H Y O P w
    (∀t,V t 0=0) ∧ ∀t,
    entry (t+1) 0=((t+1:ℕ):ℝ)⁻¹ • ripple C (entry t 0) ∧
    entry (t+1) 1=((t+1:ℕ):ℝ)⁻¹ • (ripple C (entry t 1)+
      (∑j∈antidiagonal t,arbor C (V j.1 1) (entry j.2 0))+
      ∑j∈antidiagonal t,arbor C.transpose (V j.1 1) (entry j.2 0)):=by
  intro A p K S F H Y O P C V entry
  have virgin:∀j,V j 0=0:=bare_abr _ (pack_zero S R.alloy.B.ratio)
  exact ⟨virgin,fun t=>grading C V (srCold w (extractV G S F Y)) virgin t⟩

end YM.Integration.WilsonThermometerUnitFilingWeakOneVertex
