import YM.Integration.WilsonSeparatedOriginalSlabMeasuredProxy
import YM.Integration.WilsonMacroscopicRichChildRegistration
import YM.Integration.WilsonReportHarvestSlabCenteredPhysical

/-! One deposited zero-grade physical field is tested against the submitted source on the same held Wilson fibre at every earlier filing date. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalSlabHeldProxy
open Function Filter MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Address RG05Readout.Native RG05Readout.View
open Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi Push.GridApprox
open PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station Ribbons
open RG16.Literal Trace.Physical.GermGraph Extra.Histories.Relay WilsonLimitConstruction PhysicalNext
open WilsonSeparatedOriginalSlabMeasuredProxy WilsonSeparatedOriginalSlabFiledFilm
open private pushed from YM.Integration.WilsonReportHarvestSlabCenteredPhysical
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge}(R:Run G){u₀ b N per:ℕ}
set_option quotPrecheck false
local notation "C"=>R.family
local notation "A"=>(C).path

lemma normalized {i:ℕ}(hi:i≤N)(f:Cut C N per)(V:Config G ((C).side i per)):
    credit C N per 0 f i hi V/(((A).rep N per i).eval V:ℂ)=actualTransport C (N:=N) f hi V:=by
  simp only [credit,pow_zero,one_smul,actualTransport,Complex.real_smul,Complex.ofReal_inv,div_eq_inv_mul,pushed]
  congr 2;funext U;exact congrArg (fun q:ℝ=>(q:ℂ)*f U) (congrFun (R.makes.wilson.starts N per).2 U).symm

theorem original {top:b<N}{η bound:ℝ}(f:Cut C N per)(file:Filing R f u₀ 0 top η bound):
    ∃fee:ℝ,fee≤bound ∧ ∃z:(C).label 0,
      let E:=WilsonMacroscopicRichCaptureFilingBudget.capital C b fee η
      Next.UVStress.quota C 0 b N per z≤2*E ∧ ∀ j : ℕ, u₀ ≤ j → ∀(ib:j≤b)(_door:Opened C 0 j per),
        let h:=ib.trans top.le
        Booked C N per 0 f j h ∧ Booked C N per 0 ((C).O N per z 0) j h ∧
        ‖actualTransport C (N:=N) f h 1-actualTransport C (N:=N) ((C).O N per z 0) h 1‖≤E/gainChart A b j:=by
  obtain ⟨fee,price,_,z,quota,dates⟩:=file
  refine ⟨fee,price,z,quota,?_⟩
  intro j lower ib door
  let h:=ib.trans top.le
  obtain ⟨primary,cost⟩:=dates j lower ib door
  obtain ⟨named,name⟩:=WilsonMacroscopicRichChildRegistration.issued C R.makes z door h
  refine ⟨primary,named,?_⟩
  let phi:=fitting ( «C»:=R.family) 0 N per j R.makes door h
  let v:=topReport C N per 0 R.makes j door h f
  let w:=topReport C N per 0 R.makes j door h ((C).O N per z 0)
  have fv:(phi v) 0=actualTransport C (N:=N) f h 1:=(unit R door h f primary).trans (normalized R h f 1)
  have fw:(phi w) 0=actualTransport C (N:=N) ((C).O N per z 0) h 1:=(unit R door h _ named).trans (normalized R h _ 1)
  have small:‖(phi (v-w)) 0‖≤((C).labels.level 0).coeffSize (phi (v-w)):=Finset.single_le_sum (fun _ _=>norm_nonneg _) (Finset.mem_univ _)
  rw [←fv,←fw,←Pi.sub_apply,←map_sub]
  apply small.trans
  change mCost C 0 N per j (v-w)≤_
  dsimp only [w];rw [name];exact cost

end YM.Integration.WilsonSeparatedOriginalSlabHeldProxy
