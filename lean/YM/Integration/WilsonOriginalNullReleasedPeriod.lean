import YM.Integration.WilsonOriginalNullReleasedOrientation

noncomputable section
namespace YM.Integration.WilsonOriginalNullReleasedPeriod
open Function Filter Lattice Wilson RG Labels Source Trace.Physical GermGraph
open PhysicalNext.Repeat.Legato
open scoped Topology

/-- This invoice is taken on the physical side at the fixed reporting radius.
Every other endpoint factor is fixed before the two regulators. -/
theorem original {G:Gauge}(R:Run G)(d k:ℕ)(f:Extraction.Order)(fee:ℝ):
    Tendsto (fun z:ℕ×ℕ=>fee*invoice (C:=R.family) d k z.2*stock R.family k) f.fuse (𝓝 0):=by
  let C:=R.family
  let B:=plank C k
  have per:Tendsto (Prod.snd:ℕ×ℕ→ℕ) f.fuse atTop:=by
    apply tendsto_atTop.mpr
    intro n
    change f.late (fun _ p=>n≤p)
    exact (f.per.cofinal.eventually_ge_atTop n).mono fun _ h=>Eventually.of_forall fun _=>h
  have strict:StrictMono (fun p=>((C.side k p).val:ℕ)):=by
    intro a b hab
    change (C.S.period a).val*(C.S.denominator k).val < (C.S.period b).val*(C.S.denominator k).val
    exact Nat.mul_lt_mul_of_pos_right (C.S.period_strict hab) (C.S.denominator k).property
  have side:Tendsto (fun z:ℕ×ℕ=>((C.side k z.2).val:ℝ)) f.fuse atTop:=
    (tendsto_natCast_atTop_atTop.comp strict.tendsto_atTop).comp per
  have den:0<10*(4*(B.B:ℝ)+2):=by positivity
  have down:=tendsto_atBot_add_const_left f.fuse (2*B.supportExponent)
    (tendsto_neg_atTop_atBot.comp ((side.const_mul_atTop B.exponent_pos).atTop_div_const den))
  have seam:=Real.tendsto_exp_atBot.comp down
  have full:Tendsto (fun z:ℕ×ℕ=>invoice (C:=C) d k z.2) f.fuse (𝓝 0):=by
    simpa [invoice,cut,Germ.wraps,B,sub_eq_add_neg,Function.comp_def] using
      seam.const_mul (price (C:=C) d)
  simpa only [mul_zero,zero_mul] using (full.const_mul fee).mul_const (stock C k)

end YM.Integration.WilsonOriginalNullReleasedPeriod
end
