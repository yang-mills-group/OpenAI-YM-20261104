import YM.Integration.WilsonFirstReceivedGalleryRegular
import YM.RG02.Marker.Partition
import YM.QuadraticLocal.Tariff.Measure

/-! The complete normalized read on a genuinely clear arbitrary group field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalOccupiedClear
open Finset Lattice RG Wilson Marker Multi QuadraticLocal Ac Source Labels Extra.Histories
open QuadraticLocal.Fusion.Attached Push.Local Planned.GuardedAtom Comparison.RG02.Cumulants
open scoped Classical BigOperators
variable {G:Gauge} {n:Side} {V X I:Type} [DecidableEq V] [Fintype V]
    {o:V→Site n} {J:Census V} {P:Rep G n} {w:V→ℝ}

theorem original (L:Gallery X I o P J) (hw:∀v,0<w v)
    (regular:L.E.Paid w P.p.B P.p.supportExponent 1)
    (x:X)(s:J.Mode)(U:Config G n)(clear:flags P.p.threshold U=∅):
    Poly.toll w s * ‖(((P.eval U:ℂ)⁻¹) • L.density x U).part s‖ ≤ (shards J s).card:=by
  have vacuum:(P.eval U:ℂ)=(Real.exp (P.exponent U):ℂ):=by
    simp [Rep.eval,P.activities.gas_one P.p clear]
  rw [Gallery.density,WilsonFirstReceivedGalleryRegular.clear L x U clear,mul_one,vacuum,
    smul_smul,inv_mul_cancel₀ (by exact_mod_cast (Real.exp_ne_zero (P.exponent U))),one_smul]
  have each(t:Hot J): Poly.toll w t.val * ‖(L.E.log x U).part t.val‖ ≤ 1:=by
    obtain ⟨v,hv⟩:=t.property
    exact WilsonFirstReceivedGalleryRegular.occupied L.E regular P.p.exponent_pos.le hw x U t.val v hv
  have shard (q:(parts J).Mode)(ok:q∈shards J s):
      Poly.toll w s*‖∏t∈q.val,(L.E.log x U).part t.val‖ ≤ 1:=by
    have split : Poly.toll w s=∏t∈q.val,Poly.toll w t.val:=by
      rw [←show unionOf q=s from (mem_filter.mp ok).2]
      exact prod_biUnion (parts_wise q)
    rw [split,norm_prod,←prod_mul_distrib]
    exact prod_le_one (fun t _=>mul_nonneg (Poly.worth hw _).le (norm_nonneg _)) (fun t _=>each t)
  rw [pass_partition _ (L.E.quiet_of_hasSum x U (regular.sums P.p.exponent_pos.le hw x U))]
  calc
    _ ≤ Poly.toll w s * ∑p∈shards J s,‖∏t∈p.val,(L.E.log x U).part t.val‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le ..) (Poly.worth hw _).le
    _ = ∑p∈shards J s,Poly.toll w s * ‖∏t∈p.val,(L.E.log x U).part t.val‖:=mul_sum .. 
    _ ≤ ∑_∈shards J s,(1:ℝ):=sum_le_sum (fun q hq=>shard q hq)
    _ = _:=by simp

end YM.Integration.WilsonOriginalOccupiedClear
end
