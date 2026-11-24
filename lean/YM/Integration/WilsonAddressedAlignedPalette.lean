import YM.Integration.WilsonThermometerOwnOffsetField
import YM.Trace.Physicalv2.GermSplit
import YM.Integration.WilsonThermometerWeakPanelExchange

/-! On the aligned physical child the primary slot has the intrinsic germ of its literal factory entry. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedAlignedPalette
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox Push.Local
open PhysicalNext.Repeat.Legato MergeProof Accent Trace.Physical Trace.Physical.GermGraph
open ProjectorNext.Equivariance Work.G08 Next.Rank
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetCylinder WilsonThermometerOffsetResidue
open WilsonThermometerOffsetLedger WilsonThermometerOwnOffsetField
open scoped BigOperators Classical Topology
variable {G:Gauge} (R:Run G) {k N p d:ℕ}
local notation "Rf" => R.family
local notation "T" => R.family.factory d N p
local notation "F" => R.family.labels.level d

private theorem push_scale {c f:Side} (P:StepData c f) (β:ℝ) (D:Config G f→ℂ) (a:ℂ):
    P.push β (a•D)=a•P.push β D:=by
  funext V
  simp only [StepData.push,Pi.smul_apply,smul_comm _ a,integral_smul]

private theorem dyes_scale (hk:k≤N) (D:Config G ((Rf).side N p)→ℂ) (a:ℂ):
    dyes Rf k N p hk (a•D)=a•dyes Rf k N p hk D:=by
  unfold dyes
  induction hk using Nat.decreasingInduction with
  | self =>
    rw [gust_base,gust_base];funext U;change _*(a*D U)=a*(_*D U);ring
  | of_succ i hi ih =>
    rw [gust_step _ _ _ _ _ hi,gust_step _ _ _ _ _ hi,ih,push_scale]

theorem density (hk:k≤N) (base:(Rf).ref d≤k) (v:(Rf).label d):
    ((T).entries k v).density 0 ((Rf).localSection d) ((Rf).path.rep N p k)=
      dyes Rf k N p hk (((Rf).S.a k:ℂ)^d • (Rf).O N p ((T).terminal v) 0):=by
  have certified:(T).Based ((Rf).params) ((Rf).localSection d) ((Rf).ref d):=R.makes.calibrated d N p (base.trans hk)
  rw [dyes_scale]
  revert base
  induction hk using Nat.decreasingInduction with
  | self =>
    intro _
    unfold dyes;rw [gust_base];funext U
    refine (certified.encode v U).trans ?_
    simp only [Family.O,TransferData.cylinder,LinearEquiv.symm_apply_apply,Pi.smul_apply,smul_eq_mul]
    ring
  | of_succ i hi ih =>
    intro old
    refine (certified.unnormalized i old hi v).trans ?_
    rw [ih (old.trans (Nat.le_succ i))]
    unfold dyes;rw [gust_step _ _ _ _ _ hi,push_scale,smul_smul]
    have bill:((Rf).S.block i).val^d*((Rf).S.a (i+1):ℂ)^d=((Rf).S.a i:ℂ)^d:=by
      have ne:(((Rf).S.block i).val:ℂ)≠0:=by exact_mod_cast ((Rf).S.block i).property.ne'
      rw [(Rf).S.a_step];push_cast;rw [←mul_pow]
      congr 1
      exact mul_div_cancel₀ _ ne
    rw [bill]

private theorem zero_parent {n m:Side} (g:Ratio n m):g.parent 0=0:=by
  have ar:lift (0:Site g.count)=0:=by funext a;simp [Lattice.lift]
  have assembled:g.assemble (0,0)=0:=by
    change g.root 0+Lattice.wrap _ (lift (0:Site g.count))=0
    rw [map_zero,ar,map_zero,add_zero]
  rw [←assembled,g.assemble_parent]

theorem primary {base:ℕ} {D:Rail Rf} {B:ℕ→ℕ→ℝ} {V:Sight Rf d p} {r:Emblems Rf d}
    (enrolled:Enrolled R.makes D B base N p d (digits R N p 0) V r) (hk:k≤N) (entered:base≤k)
    (steps:∀e≤d,(Rf).ref e≤N) (opened:Opened Rf d k p) (y:Palette Rf d):
    let t:=primaryLetter d
    fitting d N p k R.makes opened hk (finer r hk y t)=y t:=by
  let t:=primaryLetter d
  obtain ⟨X,Q,proj,Xok,fee,Qok,Qfee,delta,issued⟩:=WilsonThermometerOwnOffsetField.actual R N p k 0 enrolled entered hk steps y
  rw [zero_parent] at delta issued
  have as_field: X.density 0 ((Rf).localSection d) ((Rf).path.rep N p k)=
      dyes Rf k N p hk (((Rf).S.a k:ℂ)^d • (Rf).O N p ((T).terminal (finer r hk y t)) 0):=by
    have h:=delta.symm.trans issued
    simpa only [Function.comp_def,Lattice.pull_id] using h
  have full:reads d N p k X (B d k*size y):=⟨Xok,fee⟩
  have heq: value (C:=Rf) d N p k ((T).entries k (finer r hk y t))=value d N p k X:=
    (density R hk opened.post _).trans as_field.symm
  have agree:=same_page R.makes hk opened.post
    (entryOk d N p k R.makes opened.post hk (finer r hk y t)) full (EventuallyEq.of_eq heq)
  have top:page d p k X=y t:=by
    change Germ.projection _ _ (plank Rf k).threshold 0 X=_
    have vac:((Rf).path.rep N p k).p=plank Rf k:=(R.makes.wilson.represents N p k hk).vac
    rw [←vac]
    exact proj
  exact agree.trans top
end YM.Integration.WilsonAddressedAlignedPalette
end
