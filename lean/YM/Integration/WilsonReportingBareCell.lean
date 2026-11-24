import YM.Integration.WilsonReportingFiledSpecimen

/-! For each actual letter of the submitted roster the full bare site
density is exactly the original factory's encoded cutoff entry. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingBareCell
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

theorem incidence (h:C.Makes) (t:Letter d) (q:Body) (z:Site (C.side N p)) (x:C.label (kept t)) :
    stepUp (1,false) z (entrance C d N p
      (chunk t ((C.factory (kept t) N p).terminal.symm x)) 0 q) =
    (readJ t 0 q*(C.S.a N:ℂ)^(kept t)) • C.O N p x z := by
  let w:=chunk t ((C.factory (kept t) N p).terminal.symm x)
  rw [entrance_real]
  simp_rw [pulses_key _ h]
  rw [Fintype.sum_sigma,Finset.sum_eq_single t]
  · let T:=(C.factory (kept t) N p).terminal
    let M:=siteMap C (kept t) z
    change (∑ i:(C.labels.level (kept t)).Index,readJ t 0 q •
      ((C.S.a N:ℂ)^(kept t) • M (T (w t i • Size.axis (C.labels.level (kept t)) i)))) =
      (readJ t 0 q * (C.S.a N:ℂ)^(kept t)) • M x
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


def centered (C:Family G) {d:ℕ} (t:Letter d) (v:C.label (kept t)) (N p j:ℕ) :
    Body→Goods G (C.side j p) :=
  pulseOut (glyph (readJ t 0) (invoice ((C.factory (kept t) N p).entries j v) 0
    (C.localSection (kept t)) (C.path.rep N p j)))

theorem bare (h:C.Makes) {N p:ℕ} (starts:∀ e ≤ d,C.ref e ≤ N)
    (t:Letter d) (v:C.label (kept t)) :
    pulseOut (basisTop C d N p (chunk t v))=centered C t v N p N := by
  let T:=(C.factory (kept t) N p).terminal
  funext f X
  have entered:=incidence h t f (0:Site (C.side N p)) (T v)
  have neutral (g:Goods G (C.side N p)) : stepUp (1,false) 0 g=g := Motion.dance_nil g
  have unfiled : (C.factory (kept t) N p).terminal.symm (T v)=v := T.symm_apply_apply v
  rw [neutral,unfiled] at entered
  have row:=congrFun entered X
  change entrance C d N p (chunk t v) 0 f X =
    (readJ t 0 f*(C.S.a N:ℂ)^(kept t))*C.O N p (T v) 0 X at row
  change (basisTop C d N p (chunk t v) f).1 X=
    readJ t 0 f*(((C.factory (kept t) N p).entries N v).density 0 (C.localSection (kept t)) (C.path.rep N p N) X)
  rw [basis_agrees C d N p h starts f X,row,(h.calibrated (kept t) N p (starts _ (Nat.sub_le ..))).encode v X]
  have actual : C.O N p (T v) 0 X=Source.initial (C.localSection (kept t)) C.path N p v 0 X := by
    simp only [Family.O,TransferData.cylinder,T,LinearEquiv.symm_apply_apply]
  rw [actual]
  ring

end YM.Integration.WilsonReportingBareCell
