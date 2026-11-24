import YM.Integration.WilsonReportingRegulatedFactory
import YM.Integration.WilsonReportingSpineCharge
import YM.Integration.WilsonReportingUnitOrbit
import YM.RG05Readout.Petals.Pan

/-! The complete finite Petals field of the returned reporting chart is the
actual atRef specimen on every fine Wilson configuration. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingFiledSpecimen
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories Cells Overlay
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker RG05Readout Address Native View Bid Pressure Copper Motion
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station Ribbons
open Records Basket Halls Shadow Flatten Pulse Extraction Push.RelayDifference Petals Spec RG12 RG17
open WilsonReportingUnitOrbit
open scoped BigOperators Classical
variable {G:Gauge} {C:Family G} {d N p m:ℕ}

private def siteMap (C:Family G) (d:ℕ) (z:Site (C.side N p)) :
    C.label d →ₗ[ℂ] Goods G (C.side N p) :=
  (C.linearO N p d z).mk' (fun x=>C.O N p x z)

private theorem at_site (h:C.Makes) (q:Body) (z:Site (C.side N p)) (x:C.label d) :
    stepUp (1,false) z (entrance C d N p
      (chunk (primary d) ((C.factory d N p).terminal.symm x)) 0 q) =
    (readJ (primary d) 0 q*(C.S.a N:ℂ)^d) • C.O N p x z := by
  let t:=primary d
  let w:=chunk t ((C.factory d N p).terminal.symm x)
  rw [entrance_real]
  simp_rw [pulses_key _ h]
  rw [Fintype.sum_sigma,Finset.sum_eq_single t]
  · let T:=(C.factory d N p).terminal
    let M:=siteMap C d z
    change (∑ i:(C.labels.level d).Index,readJ t 0 q •
      ((C.S.a N:ℂ)^d • M (T (w t i • Size.axis (C.labels.level d) i)))) =
      (readJ t 0 q * (C.S.a N:ℂ)^d) • M x
    rw [← Finset.smul_sum,← Finset.smul_sum,← map_sum,← map_sum,Size.sum_axes]
    have top:w t=T.symm x:=chunk_self _
    rw [top,LinearEquiv.apply_symm_apply,mul_smul]
  · intro i _ hi
    apply Finset.sum_eq_zero
    intro j _
    change readJ i 0 q • ((C.S.a N:ℂ)^(kept i) • C.O N p
      ((C.factory (kept i) N p).terminal (w i j • Size.axis (C.labels.level (kept i)) j)) z)=0
    have empty:w i=0:=chunk_miss _ hi
    rw [empty,Pi.zero_apply,zero_smul,map_zero,(C.linearO N p (kept i) z).map_zero,smul_zero,smul_zero]
  · exact fun hi=>(hi (Finset.mem_univ t)).elim

theorem normalized (h:C.Makes) (x:C.label d) (test:Body) :
    fieldC C m N p d (chunk (primary d) ((C.factory d N p).terminal.symm
      ((phase/(C.S.a m:ℂ)^d) • x))) test =
    Petals.specimen test (Bid.upper C (fun _=>x)) N p := by
  let a:ℂ:=C.S.a N
  let c:ℂ:=C.S.a m
  have ha:a≠0:=Complex.ofReal_ne_zero.mpr (C.S.a_pos N).ne'
  have hc:c≠0:=Complex.ofReal_ne_zero.mpr (C.S.a_pos m).ne'
  have read (z:Site (C.side N p)):readJ (primary d) 0 (restricted C N p z test)*phase=test.val (C.S.place z):=by
    change readJ Suede.pip 0 (restricted C N p z test)*(Native.line Suede.pip).val 0=_
    rw [Suede.prompt]
    change test.val (C.S.place z+C.S.a N • (0:E4))=_
    rw [smul_zero,add_zero]
  funext W
  change gate C m N d * ((∑ z:Site (C.side N p),stepUp (1,false) z
    (entrance C d N p (chunk (primary d) ((C.factory d N p).terminal.symm
      ((phase/c^d) • x))) 0 (restricted C N p z test))) W) =
    a^4*((∑ z:Site (C.side N p),test.val (C.S.place z) • C.O N p x z) W)
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  calc
    _ = gate C m N d * (a^d/c^d * ∑ z:Site (C.side N p),test.val (C.S.place z)*C.O N p x z W) := by
      apply congrArg (fun y:ℂ=>gate C m N d*y)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      rw [at_site h,(C.linearO N p d z).map_smul]
      change (readJ (primary d) 0 (restricted C N p z test)*a^d)*((phase/c^d)*C.O N p x z W)=_
      rw [← read z]
      ring
    _ = _ := by
      change (a^4*(c/a)^d)*(a^d/c^d * _)=_
      rw [div_pow]
      field_simp

variable {f:Extraction.Order} {S:YM.Table C.book} {F:Final C f S} (L:Layout F)

theorem actual (r:ℝ) (w:C.label d) (U:Emblems C d) (live:L.level r ≤ N) (test:Body) :
    fieldC C (L.level r) N p d (Many.point U (WilsonReportingUpperChartPrice.returned F.room.cutoff
      (primary d) (phase • L.shift d r w) U (L.level r) N p) (L.level r) N) test =
    Petals.specimen test (Bid.upper C (fun k=>atRef L d r k w)) N p := by
  rw [WilsonReportingSpineCharge.carried F.room.cutoff live]
  change fieldC C (L.level r) N p d (chunk (primary d) (WilsonReportingFactorySingleton.upper F.room.cutoff
    d (L.level r) N p (phase • L.shift d r w))) test=_
  rw [WilsonReportingRegulatedFactory.upper L]
  exact normalized F.room.cutoff _ test

end YM.Integration.WilsonReportingFiledSpecimen
