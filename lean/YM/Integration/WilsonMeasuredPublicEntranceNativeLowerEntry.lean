import YM.Integration.WilsonMeasuredPublicEntranceNativeLowerSignal
import YM.Integration.WilsonMeasuredPublicEntranceRecordedPortfolio
import YM.Integration.WilsonMeasuredPublicEntranceRegisteredFlag
import YM.RG12.Roof.Echelons

/-! The lower engineering plane in the actual physical frame, before any thermal rescaling. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceNativeLowerEntry
open Function Filter Set Spec Table Extraction OPE OPE.Orbits Climb Trace.Pilot PhysMS Maxwell Maxwell.Free
open Extra.FD RG12.Roof
open WilsonPhysicalPositionAdmissible (Native)
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
set_option quotPrecheck false
local notation "D" => (Bel C.book).Field

open WilsonMeasuredPublicEntranceRecordedWick (Keys read coordinates)
open WilsonMeasuredPublicEntranceRecordedPortfolio (cell)

theorem billed {d:ℕ}(B:RStage C.labels d)(x y:E4)(apart:x≠y)(i:Fin (B.m+1))(z:D d)
    (tally:∀j:(C.labels.level d).Index,((C.labels.level d).grades j).2=(B.w i).2→cell x y z j=0):
    B.b.coord i z=0:=by
  have heard (j:Keys B (B.w i).2):read x y (B.b j.val) z=0:=by
    have price:=WilsonMeasuredPublicEntranceRecordedPortfolio.priced B x y j.val z 0 (le_refl _) (fun k h=>by
      rw [tally k (h.trans j.property),norm_zero])
    exact norm_le_zero_iff.mp (by simpa only [mul_zero] using price)
  rw [show B.b.coord i z=B.b.coord (⟨i,rfl⟩:Keys B (B.w i).2).val z from rfl,coordinates B x y apart]
  simp only [heard,mul_zero,Finset.sum_const_zero]

theorem original {d e:ℕ}(le:e≤d)(B:RStage C.labels d)(x y:E4)(apart:x≠y)
    (out src:Fin (B.m+1))(above:e<(B.w out).1)(s g:ℝ)(pos:0<s)
    (Z:Module.End ℂ (D d))(w:D e)
    (tally:∀j:(C.labels.level d).Index,((C.labels.level d).grades j).2=(B.w out).2→
      cell x y (Pert.Scale.gear C.labels d s (Z (B.b src))-(g:ℂ) • B.b src-
        (scheme C.labels).rise le w) j=0):
    B.b.coord out (Z (B.b src)-((g/s^(B.w out).1:ℝ):ℂ) • B.b src)=0:=by
  have eq:=billed B x y apart out _ tally
  have lower:=WilsonMeasuredPublicEntranceRecordedQuotient.upper B le out above w
  simp only [map_sub,map_smul,smul_eq_mul,lower,sub_zero,price_coord] at eq
  have positive:((s:ℂ)^(B.w out).1)≠0:=pow_ne_zero _ (by exact_mod_cast pos.ne')
  rw [map_sub,map_smul,smul_eq_mul,Complex.ofReal_div,Complex.ofReal_pow]
  field_simp
  linear_combination eq

end YM.Integration.WilsonMeasuredPublicEntranceNativeLowerEntry
end
