import YM.Integration.WilsonThermometerWeakFourLinearRows
import YM.Integration.WilsonThermometerWeakWardChambers
import YM.Integration.WilsonThermometerWeakWardSolve

/-! The full zero- and positive-grade measurable matrix survives the one common
translation used to clear the actual Haar equation on original fine sites. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakWardRows
open Function Filter Set MeasureTheory Lattice Wilson RG Labels Source Push
open Extraction RG12 RG17 Climb Trace.Pilot MergeProof Next.Extract PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat Legato Bandage Cells Next.UVStress RG05Readout RG05Readout.Address
open WilsonThermometerOffsetTrajectory WilsonThermometerWeakPanelBorn WilsonThermometerOwnOffsetField
open Push.RelayDifference
open Pert Pert.Position MS MS.Local.Physical MS.Menus MS.Land MS.Theater
open FVA2 FVA2.ColorCode Extra.FD OPE.Levy RG11.Fields Pert.RawLabels Pert.Scale
open WilsonAddressedWeakPointCells WilsonAddressedWeakCorrectedCylinder
open scoped Classical Topology BigOperators Matrix
open WilsonThermometerWeakWardReading (read)
open WilsonThermometerWeakFourLinearRows (stencil tariff entrance panel entries)
open WilsonThermometerWeakPanelBorn (arm)
variable {G:Gauge} (R:Run G) {k N p d:ℕ} {D:Deck G}
local notation "C" => R.family

def gram (z:Fin 2→Site ((C).side N p)) (r:Fin 2→Emblems C d) (hk:k≤N)
    (u:Fin 2→Glyph D d→(C).label d):Matrix (Glyph D d) (Glyph D d) ℂ:=
  fun a e=>reading R (fun _=>d) z (fun i=>chunk («C»:=R.family) (primaryLetter d) (u i (![a,e] i))) r hk full

theorem arm_field (r:Emblems C d) (hk:k≤N) (u:(C).label d) (z:Site ((C).side N p)):
    (C).O N p (entrance R (p:=p) r hk (chunk («C»:=R.family) (primaryLetter d) u)) z=arm R r hk z u:=by
  let a:ℂ:=((C).S.a k:ℂ)^d
  let e:=(C).factory d N p |>.terminal (finer r hk (chunk («C»:=R.family) (primaryLetter d) u) (primaryLetter d))
  exact (((C).linearO N p d z).mk' _).map_smul a e

theorem continuous (r:Emblems C d) (hk:k≤N) (z:Site ((C).side N p)) (u:(C).label d):
    Continuous (arm R r hk z u):=by
  rw [←arm_field]
  exact (C).continuousO N p d _ _

theorem entry (z:Fin 2→Site ((C).side N p)) (r:Fin 2→Emblems C d) (hk:k≤N)
    (u:Fin 2→Glyph D d→(C).label d) (a e:Glyph D d):
    read R d N p (z 0) (arm R (r 1) hk (z 1) (u 1 e)) (continuous R ..)
      (entrance R (p:=p) (r 0) hk (chunk («C»:=R.family) (primaryLetter d) (u 0 a)))=gram R z r hk u a e:=by
  unfold gram
  rw [WilsonAddressedWeakRootedReading.measured]
  change moment ((C).beta N p) (fun U=>(C).O N p _ (z 0) U*arm R (r 1) hk (z 1) (u 1 e) U)=
    moment ((C).beta N p) (fun U=>∏i:Fin 2,WilsonThermometerIntrinsicRoster.source R _ z _ r hk i U)
  rw [arm_field]
  congr 1
  funext U
  rw [Fin.prod_univ_two]
  rfl

theorem rows (z:Fin 2→Site ((C).side N p)) (r:Fin 2→Emblems C d) (hk:k≤N)
    (u:Fin 2→Glyph D d→(C).label d) (t:Glyph D d→ℂ) (e:Glyph D d):
    read R d N p (z 0) (arm R (r 1) hk (z 1) (u 1 e)) (continuous R ..)
      (panel R (p:=p) (r 0) hk (u 0) t)=(t ᵥ* gram R z r hk u) e:=by
  rw [WilsonThermometerWeakFourLinearRows.panel,LinearMap.comp_apply,entries]
  simp only [map_sum,map_smul,smul_eq_mul,Matrix.vecMul,dotProduct]
  apply Finset.sum_congr rfl
  intro a _
  rw [WilsonThermometerWeakWardRows.entry]

def inverseBill (K:Matrix (Glyph D d) (Glyph D d) ℂ):ℝ:=1+∑a,∑e,‖K⁻¹ a e‖
theorem fee (A K:Matrix (Glyph D d) (Glyph D d) ℂ) (near:∀i j,‖A⁻¹ i j-K⁻¹ i j‖<1):
    ∀i j,‖A⁻¹ i j‖ ≤ inverseBill K:=by
  intro i j
  have one:‖K⁻¹ i j‖≤∑c,‖K⁻¹ i c‖:=Finset.single_le_sum (fun c _=>norm_nonneg (K⁻¹ i c)) (Finset.mem_univ j)
  have two:(∑c,‖K⁻¹ i c‖)≤∑b,∑c,‖K⁻¹ b c‖:=Finset.single_le_sum (fun b _=>Finset.sum_nonneg (fun c _=>norm_nonneg (K⁻¹ b c))) (Finset.mem_univ i)
  have bound:=norm_le_norm_sub_add (A⁻¹ i j) (K⁻¹ i j)
  unfold inverseBill
  linarith only [bound,near i j,one,two]


theorem translated (z:Fin 2→Site ((C).side N p)) (t:Site ((C).side N p))
    (r:Emblems C d) (hk:k≤N) (u:(C).label d) (x:(C).label d):
    read R d N p (z 0+t) (arm R r hk (z 1+t) u) (continuous R ..) x =
      read R d N p (z 0) (arm R r hk (z 1) u) (continuous R ..) x:=by
  let U:=((C).factory d N p).terminal (finer r hk (chunk («C»:=R.family) (primaryLetter d) u) (primaryLetter d))
  exact WilsonThermometerWeakMovedExperiment.shifted R x U (((C).S.a k:ℂ)^d) (z 0) (z 1) t

theorem shifted (z:Fin 2→Site ((C).side N p)) (t:Site ((C).side N p))
    (r:Fin 2→Emblems C d) (hk:k≤N) (u:Fin 2→Glyph D d→(C).label d) (v:Glyph D d→ℂ) (i:Glyph D d):
    read R d N p (z 0+t) (arm R (r 1) hk (z 1+t) (u 1 i)) (continuous R ..)
      (panel R (p:=p) (r 0) hk (u 0) v) = (v ᵥ* gram R z r hk u) i:=by
  rw [translated]
  exact rows R z r hk u v i

end YM.Integration.WilsonThermometerWeakWardRows
end
