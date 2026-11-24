import YM.Integration.WilsonMovingForkSharpPortfolioAnnulus

noncomputable section
namespace YM.Integration.WilsonMovingForkSharpTensorSalary
open WilsonIndependentFittedMixedCash (embed)
open WilsonPhysicalMarkedDefect.RawProduct (belt)
open scoped BigOperators Classical
private theorem belt_embed (q:ℕ)(f:PowerSeries ℝ):belt q (embed f)=∑j∈Finset.range (q+1),‖PowerSeries.coeff j f‖:=by
  simp [WilsonPhysicalMarkedDefect.RawProduct.belt,embed,PowerSeries.coeff_map]
private theorem product (d m:PowerSeries ℝ)(q e:ℕ)(leaves:q≤e):
    ‖PowerSeries.coeff q (d*m)‖≤belt e (embed d)*belt e (embed m):=by
  rw [PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,belt_embed,belt_embed]
  let M:=∑j∈Finset.range (e+1),‖PowerSeries.coeff j m‖
  have M0:0≤M:=Finset.sum_nonneg fun _ _=>norm_nonneg _
  calc
    _≤∑j∈Finset.range (q+1),‖PowerSeries.coeff j d*PowerSeries.coeff (q-j) m‖:=norm_sum_le ..
    _≤∑j∈Finset.range (q+1),‖PowerSeries.coeff j d‖*M:=by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact Finset.single_le_sum (fun z _=>norm_nonneg (PowerSeries.coeff z m))
        (Finset.mem_range.mpr (Nat.lt_succ_of_le ((Nat.sub_le q j).trans leaves)))
    _=(∑j∈Finset.range (q+1),‖PowerSeries.coeff j d‖)*M:=(Finset.sum_mul ..).symm
    _≤_:=mul_le_mul_of_nonneg_right
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.succ_le_succ leaves)) (fun _ _ _=>norm_nonneg _)) M0

theorem original {I:Type*}[Fintype I](d m:I→PowerSeries ℝ)(q e:ℕ)(leaves:q≤e):
    ‖PowerSeries.coeff q (∑j,d j*m j)‖≤∑j,belt e (embed (d j))*belt e (embed (m j)):=by
  rw [map_sum]
  exact (norm_sum_le ..).trans (Finset.sum_le_sum fun j _=>product _ _ _ _ leaves)
end YM.Integration.WilsonMovingForkSharpTensorSalary
