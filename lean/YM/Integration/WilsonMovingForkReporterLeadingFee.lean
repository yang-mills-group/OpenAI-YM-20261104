import YM.Integration.WilsonMovingForkReporterFilament
import YM.PhysMS.Frame.Step

/-! Cost on the previously fixed physical leading chart, uniformly on its full finite horizon. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkReporterLeadingFee
open Function Filter Lattice Wilson RG Source Extraction Table Spec OPE
open PhysicalNext.Repeat.Legato RG17 FullVolume Climb Next.UVStress Trace.Pilot PhysMS
open GapsContact OPE.Levy Stamps Seams Ascent Trace MergeProof.East Maxwell XSpace XSpace.Normalize
open Trace.Terrace Trace.Over FVA2 FVA2.Register WilsonThermometerUnitFilingFourSquare
open YM.Push.FiniteDetection.Free
open scoped Topology Classical BigOperators
variable {G:Gauge} {C:Family G} {f:Extraction.Order} {S:Table C.book}
  (F:Final C f S) (J:ℝ→tower S) (d:ℕ)
private abbrev Space (C:Family G) (d:ℕ) := (Bel C.book).Field d
local notation "E" => Space C d

private def bill (r:ℝ) : E →ₗ[ℂ] E →ₗ[ℂ] ℂ := Levy.linear₂
  ((S.classMoment S (fun _:Fin 2=>d) (r • detectors)).compLinearMap (fun _=>(J r d).toLinearMap))

private def free : E →ₗ[ℂ] E →ₗ[ℂ] ℂ := Levy.linear₂ ((Bel C.book).classMoment
  (Bel C.book) (fun _=>d) detectors)

private theorem heard (accepted:Leading F J) (u w:E):
    Tendsto (fun r=>bill J d r u w) trail (𝓝 (free (C:=C) d u w)) :=
  leading_at F accepted (d:=fun _:Fin 2=>d) ![u,w] tendsto_id tendsto_const_nhds detectors_in

private theorem native (r:ℝ) (u:E)
    (h:Spin.realH F.room.kernel.spin (Maxwell.Free.spin_free C.labels) (J r d)):
    cost F d r (J r d u)=Real.sqrt ‖bill J d r u (Levy.reflect d u)‖ := by
  unfold cost flipField
  rw [←PhysMS.Frame.flip_coupled F d J r h u]
  apply congrArg (fun z:ℂ=>Real.sqrt ‖z‖)
  apply DFunLike.congr_arg (S.classMoment S (fun _=>d) _)
  exact funext fun j=>by fin_cases j <;> rfl

private theorem varying {I:Type*} {l:Filter I} {A:I→E →ₗ[ℂ] E →ₗ[ℂ] ℂ} {B:E →ₗ[ℂ] E →ₗ[ℂ] ℂ}
    (earn:∀ u w,Tendsto (fun i=>A i u w) l (𝓝 (B u w)))
    {p q:I→E} {v w:E} (hp:Tendsto p l (𝓝 v)) (hq:Tendsto q l (𝓝 w)):
    Tendsto (fun i=> A i (p i) (q i)) l (𝓝 (B v w)) := by
  let M i:=A i (p i)
  apply Dash.arcing (W:=fun i=>(M i).toContinuousLinearMap) (X:=(B v).toContinuousLinearMap) ?_ hq
  refine Dash.fit_plane M (B v) (fun x=>?_)
  exact Dash.arcing (Dash.fit_plane (fun i=>LinearMap.comp (LinearMap.applyₗ (R:=ℂ) x) (A i))
    (LinearMap.comp (LinearMap.applyₗ (R:=ℂ) x) B) (fun u=>earn u x)) hp

private theorem observed {I:Type*} {l:Filter I} {r:I→ℝ} {p:I→E} {v:E}
    (accepted:Leading F J) (hr:Tendsto r l trail) (hp:Tendsto p l (𝓝 v)):
    Tendsto (fun i=>cost F d (r i) (J (r i) d (p i))) l
      (𝓝 (Real.sqrt ‖Levy.free2 (C:=C) d v (Levy.reflect d v)‖)) := by
  have seed:=varying (C:=C) d (A:=fun i=>bill J d (r i)) (B:=free (C:=C) d)
    (fun u w=>(heard F J d accepted u w).comp hr) hp (Levy.reflect_limit d hp)
  have damp:= (Real.continuous_sqrt.tendsto _).comp seed.norm
  apply damp.congr'
  filter_upwards [hr.eventually (accepted.equivariant d)] with i h
  exact (native F J d (r i) (p i) h).symm

theorem original (accepted:Leading F J) :
    ∃ A:ℝ,1≤A ∧ ∀ᶠ r in trail,∀v:E,cost F d r (J r d v)≤A*‖v‖ := by
  let disk := Metric.closedBall (0:E) 1
  let bench (v:E) := Real.sqrt ‖Levy.free2 (C:=C) d v (Levy.reflect d v)‖
  have dc:IsCompact disk:=isCompact_closedBall _ _
  have hn:disk.Nonempty:=⟨0,Metric.mem_closedBall_self zero_le_one⟩
  have continuous:Continuous bench:=continuous_iff_continuousAt.mpr (fun x=>
    (Real.continuous_sqrt.tendsto _).comp (PhysMS.Frame.free_limits d (v:=x) tendsto_id).norm)
  obtain ⟨m,hm,maximum⟩ := dc.exists_isMaxOn hn continuous.continuousOn
  let A:=bench m+1
  have high:1≤A:=by have fee:0≤bench m:=Real.sqrt_nonneg _;dsimp [A];linarith only [fee]
  have filled:∀ᶠ r in trail, ∀ x∈disk,cost F d r (J r d x)≤A := by
    apply PhysMS.Frame.compact_event ℝ dc
    intro x inside
    have room:bench x<A:=(maximum inside).trans_lt (lt_add_one _)
    exact (observed F J d accepted (r:=Prod.fst) (p:=Prod.snd)
      (l:=trail ×ˢ 𝓝 x) tendsto_fst tendsto_snd).eventually (ge_mem_nhds room)
  refine ⟨A,high,?_⟩
  filter_upwards [filled] with r sales u
  rcases eq_or_ne u 0 with rfl|nonzero
  · simp only [map_zero,cost_zero,norm_zero,mul_zero,le_refl]
  have live:=norm_pos_iff.mpr nonzero
  let w:=((↑‖u‖⁻¹:ℂ) • u)
  have unit:‖w‖=1:=by unfold w;rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg (by positivity),inv_mul_cancel₀ live.ne']
  have offer:=sales w (mem_closedBall_zero_iff.mpr unit.le)
  have back:cost F d r (J r d w)=‖u‖⁻¹*cost F d r (J r d u):=by
    unfold w;rw [map_smul,cost_hom,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
  rw [back,inv_mul_le_iff₀ live,mul_comm ‖u‖ A] at offer
  exact offer

end YM.Integration.WilsonMovingForkReporterLeadingFee
end
