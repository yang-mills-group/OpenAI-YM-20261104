import YM.Integration.WilsonMatrixOriginalGermMarket

/-! The source issued on a complete captured germ has a uniform physical quota at that same
date. The upper cutoff and period do not enter the right hand side. -/
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalGermRedemption
open Filter Finset Lattice Wilson RG RG12 RG17 Labels Source FullVolume Table Climb Spec
open MS.Local.Physical MS.Menus FVA2 PhysicalNext.Repeat.Legato Next.Rank.Price
open Trace.Physical.GermGraph WilsonMatrixTicketLanesNativePrices WilsonMatrixOriginalIndependentColumns
open WilsonMatrixTicketLanesRegulatorColumn WilsonMatrixOriginalGermMarket
open scoped Classical BigOperators
variable {G:Gauge}

private theorem inverse_size (C:Family G) (d N p m:ℕ) (H:C.Makes) (opened:Opened C d m p)
    (live:m≤N) (x:C.label d):
    let q:=(C.factory d N p).entries m x
    (C.labels.level d).coeffSize q.x≤2*(C.labels.level d).coeffSize (page d p m q):=by
  intro q
  let F:=C.labels.level d
  have diff:=measured_diff d N p m H opened.post live (entryOk d N p m H opened.post live x)
  change F.coeffSize (page d p m q-q.x) ≤ invoice (C:=C) d m p*(stock C m*F.coeffSize q.x) at diff
  have nz:=Work.G08.size_nonneg F q.x
  have deal:=mul_le_mul_of_nonneg_right opened.small.le nz
  rw [mul_assoc] at deal
  have tri:=count_sub (C:=C) (d:=d) (page d p m q) (page d p m q-q.x)
  rw [sub_sub_cancel] at tri
  linarith only [diff,deal,tri,nz]

private theorem mesh (X:Frame G 4) (t b:ℝ) (pos:0≤t) (leq:t≤b) (large:1≤b) (x:X.Coeff):
    X.coeffSize (X.scaled t x)≤b^4*X.coeffSize x:=by
  unfold Frame.coeffSize;rw [mul_sum];apply sum_le_sum;intro i _
  rw [Frame.scaled_apply,norm_mul,Complex.norm_real,Real.norm_of_nonneg (pow_nonneg pos _)]
  exact mul_le_mul_of_nonneg_right ((pow_le_pow_left₀ pos leq _).trans
    (pow_le_pow_right₀ large (Planned.PrimaryIntegral295.Film.second_fits X i))) (norm_nonneg _)

variable (R:Run G) (B:Deck G) {f:Extraction.Order} {S:Table R.family.book}
    (F:Final R.family f S) (L:Layout F) {m N p:ℕ}

def calibrated (opened:Opened R.family 4 m p) (live:m ≤ N) :=
  (fitting 4 N p m R.makes opened live).trans (WilsonMatrixOriginalGermAnchor.clocked R m (shrink R.family m N p)
    (shrink_pos R.family R.makes live p).ne')

theorem named (opened:Opened R.family 4 m p) (live:m ≤ N) (i:Glyph B 4):
    let w:=WilsonMatrixOriginalGermAnchor.issued R B (N:=N) (p:=p) (calibrated R opened live) i
    (R.family.labels.level 4).scaled (shrink R.family m N p) (normalized R m N p w)=column (warehouse R) B 4 i:=by
  intro w
  let q:=calibrated R opened live
  let T:=(R.family.factory 4 N p).terminal
  have direct:q (T.symm w)=column (warehouse R) B 4 i:=by
    change q (T.symm (T (q.symm _)))=_
    simp only [LinearEquiv.symm_apply_apply,LinearEquiv.apply_symm_apply]
  change (WilsonMatrixOriginalGermAnchor.clocked R m (shrink R.family m N p) (shrink_pos R.family R.makes live p).ne')
    (fitting 4 N p m R.makes opened live (T.symm w))=_ at direct
  rw [fitting_apply] at direct
  exact direct

include L in
theorem purchase (opened:Opened R.family 4 m p) (live:m ≤ N) (i:Glyph B 4):
    let w:=WilsonMatrixOriginalGermAnchor.issued R B (N:=N) (p:=p) (calibrated R opened live) i
    (R.family.S.a m^4)⁻¹*Next.UVStress.quota R.family 4 m N p w ≤
      2*(2*R.family.path.levels.clock.monitor m)^4*(R.family.labels.level 4).coeffSize (column (warehouse R) B 4 i):=by
  intro w
  let X:=R.family.labels.level 4
  let t:=shrink R.family m N p
  have pos:0<t:=shrink_pos R.family R.makes live p
  have limit:t⁻¹ ≤ 2*R.family.path.levels.clock.monitor m:=shrink_min R.family R.makes live p
  have tall:1≤R.family.path.levels.clock.monitor m:=Real.one_le_exp (sq_nonneg _)
  have bound:=mesh X t⁻¹ _ (inv_nonneg.mpr pos.le) limit (by linarith only [tall]) (column (warehouse R) B 4 i)
  have col:=named R B opened live i
  have restore:X.scaled t⁻¹ (column (warehouse R) B 4 i)=normalized R m N p w:=by
    rw [←col]
    exact (WilsonMatrixOriginalGermAnchor.thermostat X t pos.ne').left_inv _
  rw [restore] at bound
  have inverse:=inverse_size R.family 4 N p m R.makes opened live ((R.family.factory 4 N p).terminal.symm w)
  have scale : RG12.mass R.family 4 (entry R 4 m N p w) ≤ 2*X.coeffSize (normalized R m N p w):=by
    let c:ℂ:=(↑(R.family.S.a m^4):ℂ)⁻¹
    let q:=(R.family.factory 4 N p).entries m ((R.family.factory 4 N p).terminal.symm w)
    change X.coeffSize (c • q.x) ≤ 2*X.coeffSize (c • page 4 p m q)
    rw [Extra.Histories.Size.smul,Extra.Histories.Size.smul]
    exact (mul_le_mul_of_nonneg_left inverse (norm_nonneg c)).trans_eq (by ring)
  rw [cost R F L 4 m N p opened.post live w] at scale
  exact scale.trans ((mul_le_mul_of_nonneg_left bound (by norm_num:0≤(2:ℝ))).trans_eq (by ring))

end YM.Integration.WilsonMatrixOriginalGermRedemption
