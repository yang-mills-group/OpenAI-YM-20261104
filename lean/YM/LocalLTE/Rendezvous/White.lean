import YM.LocalLTE.Rendezvous.League
import YM.LocalLTE.Rendezvous.Porthole
/-! # input readout on passing configurations; compatibility with conditioned source log. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Pass
open Function Filter Set Lattice RG Pressure Wilson Finset MeasureTheory
open Push RG Shoot Org Extra.Iteration
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open PhysicalNext.Repeat.Mallow
variable {G:Gauge}{n:Side}{R:Rep G n}
variable {V:Type}[DecidableEq V][Fintype V] {X:Marker.Census V} (A:Overlay.Bands X R)(U:Config G n)
include A
omit [Fintype V] in
lemma sheds (h:flags R.p.threshold U=∅): A.cluster U=1:=by
   unfold Overlay.Bands.cluster; rw [tsum_eq_single ∅]; unfold Overlay.Bands.packet; rw [if_pos]; simp; simp [Activities.admissible,h]
   intro s he; have hz:¬R.activities.admissible R.p U s:=by
       intro ha; obtain ⟨i,hi⟩:= Finset.nonempty_iff_ne_empty.mpr he; obtain ⟨j,hj⟩:=(R.activities.forced i).inventory_ne
       exact Finset.notMem_empty _ ((ha.2.trans h) ▸ (Finset.mem_biUnion.mpr ⟨i,hi,hj⟩))
   unfold Overlay.Bands.packet; rw [if_neg hz]

lemma stepClean {c:Side}{S: StepData n c}{x:ℝ}{f: Config G c→ℝ}{p: Config G c→ Marker.Poly X}(hU:flags R.p.threshold U=∅)(h:S.push x f U=R.eval U)(he:A.density U=S.push x p U) : 0<S.push x f U ∧ (S.push x f U)⁻¹ • S.push x p U=Marker.Poly.pass (A.extra U):=by
    let a:= Real.exp (R.exponent U); rw [h,← he, Rep.eval, Activities.gas_one _ _ hU,mul_one]; refine ⟨Real.exp_pos _,?_⟩
    unfold Overlay.Bands.density; rw [sheds A U hU,mul_one]; change a⁻¹ • (a • Marker.Poly.pass (A.extra U)) = _; rw [inv_smul_smul₀ (Real.exp_pos _).ne']
end YM.LocalLTE.Pass
