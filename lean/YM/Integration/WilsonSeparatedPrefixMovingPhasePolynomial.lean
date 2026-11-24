import YM.Integration.WilsonSeparatedPrefixMovingMomentMaster
 
/-! Exact real polarization of the translated outer profile. Each term of
the actual Taylor polynomial uses a bounded genuine center moment and the
Cartesian derivative of that original smooth profile at the same lattice
point. Finite sums preserve the measured field and its signs. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingPhasePolynomial
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore MeasureTheory
open scoped BigOperators Topology Classical



open WilsonCoeffUV.Layout
open WilsonIndependentFittedExteriorProfile (home)
open WilsonIndependentMatchedCoverProfile (word)

open Set
open scoped ContDiff

open WilsonSeparatedPrefixMovingCenterMoments (monomial)
open WilsonSeparatedPrefixMovingExteriorTaylor (jet)
variable {k d:ℕ}

theorem coordinates (v:Point4):v=∑a:Axis,v a • Embroider.dot a:=by
  funext i
  simp [Embroider.dot,Finset.sum_apply,Pi.smul_apply,Pi.single_apply]

theorem contract (t:ℝ)(z o:CellR)
    (A:ContinuousMultilinearMap ℝ (fun _:Fin d=>Point4) ℝ):
    A (fun _=>t • (z.val-o.val))=t^d*
      ∑a:Fin d → Axis,monomial o a z*A (Embroider.dot ∘ a):=by
  let M:=A.toMultilinearMap
  have all (f:Fin d → Point4):M (fun i=>t • f i)=t^d*M f:=by
    simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] using
      M.map_smul_univ (fun _=>t) f
  rw [show A (fun _=>t • (z.val-o.val))=t^d*M (fun _=>z.val-o.val) from all _]
  congr 1
  calc M (fun _=>z.val-o.val)=M (fun _:Fin d=>∑a:Axis,(z.val-o.val) a • Embroider.dot a):=
        congr_arg M (funext fun _=>coordinates _)
       _ = _:=by
         rw [MultilinearMap.map_sum_finset,Fintype.piFinset_univ]
         exact Finset.sum_congr rfl fun a _=>M.map_smul_univ (fun i=>(z.val-o.val) (a i)) (Embroider.dot ∘ a)

private theorem ray {f:Point4 → ℝ}(k:ℕ)(x v:Point4)(s:ℝ)(smooth:ContDiffAt ℝ k f (x+s • v)):
    iteratedDeriv k (fun t:ℝ=>f (x+t • v)) s=iteratedFDeriv ℝ k f (x+s • v) (fun _=>v):=by
  let L:=ContinuousLinearMap.toSpanSingleton ℝ v
  let g:=fun z:Point4=>f (x+z)
  have shifted:ContDiffAt ℝ k g (L s):=smooth.comp (L s) (contDiffAt_const.add contDiffAt_id)
  rw [iteratedDeriv_eq_iteratedFDeriv]
  change iteratedFDeriv ℝ k (g ∘ L) s (fun _=>1)=_
  rw [YM.ConnectedActivityE6.Blaze.linear_pull L shifted]
  simp [g,L,ContinuousMultilinearMap.compContinuousLinearMap_apply,iteratedFDeriv_comp_add_left]

theorem original (g:Point4 → ℝ)(smooth:ContDiff ℝ k g)(x:Point4)(t:ℝ)(z o:CellR):
    jet g x (t • (z.val-o.val)) k=
      ∑n∈Finset.range (k+1),(n.factorial:ℝ)⁻¹*t^n*
        ∑a:Fin n → Axis,monomial o a z*iteratedFDeriv ℝ n g x (Embroider.dot ∘ a):=by
  let v:=t • (z.val-o.val)
  let f:=fun τ:ℝ=>g (x+τ • v)
  have regular:ContDiff ℝ k f:=smooth.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have uni:UniqueDiffOn ℝ (Icc (0:ℝ) 1):=uniqueDiffOn_Icc zero_lt_one
  have mem:(0:ℝ)∈Icc (0:ℝ) 1:=by simp
  change taylorWithinEval f k (Icc 0 1) 0 1=_
  rw [taylor_within_apply]
  refine Finset.sum_congr rfl fun n hn=>?_
  have small:n ≤ k:=Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  have one (s:ℝ):ContDiffAt ℝ n g (x+s • v):=(smooth.of_le (Nat.cast_le.mpr small)).contDiffAt
  rw [iteratedDerivWithin_eq_iteratedDeriv uni (regular.of_le (Nat.cast_le.mpr small)).contDiffAt mem]
  have step:=ray n x v 0 (one 0)
  simp only [zero_smul,add_zero] at step
  change _ • (iteratedDeriv n f 0)=_
  rw [show iteratedDeriv n f 0=_ from step,contract t z o]
  simp [smul_eq_mul,mul_assoc]

end YM.Integration.WilsonSeparatedPrefixMovingPhasePolynomial
