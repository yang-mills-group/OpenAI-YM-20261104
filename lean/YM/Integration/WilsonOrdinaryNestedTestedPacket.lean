import YM.Integration.WilsonOrdinaryNestedTestedMS
import YM.Integration.WilsonPublicForkProfile
/-! The true normalized packet and the finite independent matrix are integrated
on the same separated vertex. The radius threshold precedes the test. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOrdinaryNestedTestedPacket
open Function Set Filter MeasureTheory Spec Extraction Table PhysicalNext.Repeat.Legato Climb
open OPE OPE.Log OPE.Orbits OPE.Orbits.Reader PhysMS Trace.Pilot RG17 Maxwell XSpace Pert Pert.Position
open FVA2 FVA2.Register MS MS.Theater WilsonOrdinaryNestedBasis WilsonPositionHomogeneousFrame
open MS.Land MS.Fleet MS.Menus XSpace.Normalize
open scoped Classical BigOperators Topology ContDiff
variable {G:Gauge} {R:PhysicalNext.Repeat.Legato.Run G} {f:Extraction.Order} {S:Table R.family.book}
    (F:Final R.family f S) (J:ℝ→PhysMS.tower S) (Z:WilsonPrescription G)
    (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (ν:ℝ)
    (Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    {simple:G.Simple} {σ:Prescription (Press.portDeck G)} {dial:Bool} (ms:Main.Match Z simple M σ dial)
    {n:ℕ} (d:Fin n→ℕ)
local notation "pub" => homogeneous F J Z
local notation "θ" => reading F J Z

theorem packet (v:Labels S d) (h:ℕ) (r:ℝ) (z:Points n)
    (margin:∀k≤h,orbitMargin Q.port k (posed r z) 0):
    ContinuousAt (fun x:Points n=>Q.packet h (posed r x) v 0) z:=by
  unfold Reader.packet
  apply ContDiffAt.continuousAt (𝕜:=ℝ) (n:=∞)
  apply ContDiffAt.sum
  intro i _
  let fi:ℕ:=(i:Fin (h+1)).val
  have hi:fi≤h:=Nat.le_of_lt_succ i.isLt
  apply (((F.sector.derivatives.rise hi).toContinuousLinearMap).restrictScalars ℝ).contDiff.contDiffAt.comp (𝕜:=ℝ)
  refine ContDiffAt.comp (g:=fun y:(Fin n→E4)×E4=>Q.fresh fi y.1 y.2 v) (f:=fun x:Points n=>(posed r x,(0:E4))) z
    (Q.fresh_smooth fi _ _ v (margin fi hi)) ?_
  refine ContDiffAt.prodMk ?_ contDiffAt_const
  unfold posed
  apply contDiffAt_pi.mpr
  intro i
  fun_prop

include ms in
theorem original (fac:Services R.family f S) (h q:ℕ) (K:Set (Points n)) (compact:IsCompact K)
    (clear:K⊆conf n) (c:Choice G d):
    ∀ᶠr in trail,
      (∀z∈K,ContinuousAt (fun x=>gap (Q:=Q) (J:=J) Z M ν d h q r x (axes (R:=R) d c)) z) ∧
      ∀ψ:Test n,tsupport (ψ:Points n→ℂ)⊆K →
        (∫x:Points n,ψ x • gap (Q:=Q) (J:=J) Z M ν d h q r x (axes (R:=R) d c)) =
          (pub r h).symm (basket Q h (Frame.born pub r (axes (R:=R) d c)) r ψ) -
          WilsonMSDictionaryVector.prediction R.family d h Z M ν (axes (R:=R) d c) ψ q (θ r):=by
  let a:=axes (R:=R) d c
  filter_upwards [WilsonPublicForkProfile.margins F Q h fac compact clear] with r marg
  let A:=((pub r h).symm.toLinearMap).toContinuousLinearMap
  let H(x:Points n):=Q.packet h (posed r x) (Frame.born pub r a) 0
  let row (x:Points n):=WilsonOrdinaryNestedMSPoint.field Z M ν R.family d h a x q (θ r)
  have Hc(x)(hx:x∈K):ContinuousAt H x:=packet F Q d _ _ _ _ (marg x hx)
  have Tc(x)(hx:x∈K):ContinuousAt row x:=
    (WilsonOrdinaryNestedTestedMS.point R Z M ν ms d h q (θ r) c x (clear hx)).continuousAt
      ((conf_open n).mem_nhds (clear hx))
  have eq(x:Points n):gap (Q:=Q) (J:=J) Z M ν d h q r x a=A (H x)-row x:=by
    unfold gap
    rw [WilsonOrdinaryNestedBasis.paid]
    rfl
  constructor
  · intro z hz
    change ContinuousAt (fun x=>gap (Q:=Q) (J:=J) Z M ν d h q r x a) z
    simp only [eq]
    exact (A.continuous.continuousAt.comp (Hc _ hz)).sub (Tc _ hz)
  · intro ψ supp
    have integrable:=RG17.localized ψ H (fun x hx=>Hc x (supp hx))
    have applied:=A.integrable_comp integrable
    have target:=RG17.localized ψ row (fun x hx=>Tc x (supp hx))
    change (∫x:Points n,ψ x • gap (Q:=Q) (J:=J) Z M ν d h q r x a) = A (∫x:Points n,ψ x • H x) - _
    simp_rw [eq,smul_sub,←A.map_smul]
    rw [integral_sub applied target,A.integral_comp_comm integrable]
    exact congrArg (A (∫x:Points n,ψ x • H x) - ·) (WilsonOrdinaryNestedTestedMS.filed R Z M ν ms d ψ h q (θ r) c)
end YM.Integration.WilsonOrdinaryNestedTestedPacket
end
