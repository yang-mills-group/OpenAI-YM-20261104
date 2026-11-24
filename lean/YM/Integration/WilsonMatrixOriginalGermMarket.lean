import YM.Integration.WilsonMatrixOriginalGermAnchor
import YM.Integration.WilsonMatrixOriginalIndependentBudget

/-! A field at the earlier observation is issued on the full normalized local germ. Its
coefficient expense is charged to the actual stage quota, before the upper volume or period. -/

noncomputable section
namespace YM.Integration.WilsonMatrixOriginalGermMarket
open Lattice Wilson RG Precision RG17 Source Labels Extraction Spec FullVolume Table Climb RG12
open MS.Local.Physical MS.Menus Trace.Physical.GermGraph FVA2 PhysicalNext.Repeat.Legato Next.Rank.Price
open WilsonMatrixTicketLanesNativePrices WilsonMatrixOriginalIndependentColumns
open WilsonMatrixTicketLanesRegulatorColumn WilsonInheritedRegisteredField Finset
open scoped Classical BigOperators
variable {G:Gauge}

private theorem page_bill (C:Family G) (d N p m:ℕ) (H:C.Makes) (opened:Opened C d m p)
    (live:m≤N) (x:C.label d):
    let q:=(C.factory d N p).entries m x
    (C.labels.level d).coeffSize (page d p m q)≤2*(C.labels.level d).coeffSize q.x:=by
  intro q
  let F:=C.labels.level d
  have diff:=measured_diff d N p m H opened.post live (entryOk d N p m H opened.post live x)
  change F.coeffSize (page d p m q-q.x) ≤ invoice (C:=C) d m p*(stock C m*F.coeffSize q.x) at diff
  have small:invoice (C:=C) d m p*stock C m≤1:=opened.small.le.trans (by norm_num)
  have settle:=mul_le_mul_of_nonneg_right small (Work.G08.size_nonneg F q.x)
  rw [mul_assoc,one_mul] at settle
  calc
    _ = F.coeffSize (q.x+(page d p m q-q.x)):=by rw [add_sub_cancel]
    _ ≤ F.coeffSize q.x + F.coeffSize (page d p m q-q.x):=Extra.Histories.Size.add _ _ _
    _ ≤ F.coeffSize q.x + F.coeffSize q.x:= add_le_add le_rfl (diff.trans settle)
    _ = _ :=(two_mul _).symm

private theorem heated (F:Frame G 4) (t:ℝ) (pos:0≤t) (upper:t≤2) (x:F.Coeff):
    F.coeffSize (F.scaled t x)≤16*F.coeffSize x:=by
  unfold Frame.coeffSize
  rw [mul_sum]
  apply sum_le_sum
  intro i _
  rw [Frame.scaled_apply,norm_mul,Complex.norm_real,Real.norm_of_nonneg (pow_nonneg pos _)]
  have grade: (2:ℝ)^(F.grades i).2≤2^4:=
    pow_le_pow_right₀ one_le_two (Planned.PrimaryIntegral295.Film.second_fits F i)
  exact mul_le_mul_of_nonneg_right ((pow_le_pow_left₀ pos upper _).trans (grade.trans (by norm_num))) (norm_nonneg _)

variable (R:Run G) (B:Deck G) {f:Extraction.Order} {S:Table R.family.book} (F:Final R.family f S) (L:Layout F)

def normalized (m N p:ℕ) (w:R.family.label 4):R.family.label 4:=
  (↑(R.family.S.a m^4):ℂ)⁻¹ • page 4 p m ((R.family.factory 4 N p).entries m
    ((R.family.factory 4 N p).terminal.symm w))

def spectrum (m N p:ℕ) (w:R.family.label 4):Glyph B 4→ℂ:=
  weights (warehouse R) B 4 ((R.family.labels.level 4).scaled (shrink R.family m N p) (normalized R m N p w))

include L in
/-- All current and old coefficients together on the same earlier physical leaf. -/
theorem charge (m N p:ℕ) (opened:Opened R.family 4 m p) (live:m≤N) (w:R.family.label 4):
    ∑i,‖spectrum R B m N p w i‖≤
      (32*((R.family.S.a m^4)⁻¹*Next.UVStress.quota R.family 4 m N p w))*fare (warehouse R) B 4:=by
  let X:=R.family.labels.level 4
  let c:ℂ:=(↑(R.family.S.a m^4):ℂ)⁻¹
  let t:=shrink R.family m N p
  let q:=(R.family.factory 4 N p).entries m ((R.family.factory 4 N p).terminal.symm w)
  have positive:0≤fare (warehouse R) B 4:=sum_nonneg fun _ _=>sum_nonneg fun _ _=>norm_nonneg _
  have estimate:=page_bill R.family 4 N p m R.makes opened live ((R.family.factory 4 N p).terminal.symm w)
  have raw : X.coeffSize (normalized R m N p w)≤2*RG12.mass R.family 4 (entry R 4 m N p w):=by
    change X.coeffSize (c • page 4 p m q)≤2*X.coeffSize (c • q.x)
    rw [Extra.Histories.Size.smul,Extra.Histories.Size.smul]
    calc
      _ ≤ ‖c‖*(2*X.coeffSize q.x):=mul_le_mul_of_nonneg_left estimate (norm_nonneg _)
      _ = _:=by ring
  have factor:=heated X t (shrink_pos R.family R.makes live p).le
    (RG12.Arche.shrink_current (C:=R.family) (p:=p) R.makes live) (normalized R m N p w)
  have paid:=cost R F L 4 m N p opened.post live w
  have total:X.coeffSize (X.scaled t (normalized R m N p w))≤32*((R.family.S.a m^4)⁻¹*Next.UVStress.quota R.family 4 m N p w):=by
    rw [paid] at raw
    linarith only [raw,factor]
  exact (bounded (warehouse R) B 4 _).trans (mul_le_mul_of_nonneg_right total positive)

theorem read (simple:G.Simple) (m N p:ℕ) (opened:Opened R.family 4 m p) (live:m≤N) (w:R.family.label 4):
    let fit:=(fitting 4 N p m R.makes opened live).trans (WilsonMatrixOriginalGermAnchor.clocked R m
      (shrink R.family m N p) (shrink_pos R.family R.makes live p).ne')
    ∀o(U:Config G (R.family.side m p)), field R.makes live w o U=∑i,spectrum R B m N p w i*
      field R.makes live (WilsonMatrixOriginalGermAnchor.issued R B (N:=N) (p:=p) fit i) o U:=by
  intro fit
  obtain ⟨eq,_,binding⟩:=WilsonMatrixOriginalGermAnchor.field_at R B simple opened live
    (shrink R.family m N p) (shrink_pos R.family R.makes live p).ne' w
  rw [eq] at binding
  exact binding

end YM.Integration.WilsonMatrixOriginalGermMarket
