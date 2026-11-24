import YM.Integration.WilsonMovingForkTubeFee
import YM.Integration.WilsonMovingForkTubeRoom
import YM.Integration.WilsonSeparatedPhysicalDisc

/-! Uniform real derivative prices at every separated position, however far the
physical spectator lies from the near group. The physical input may depend on its
own date. The product of its actual reflected costs is paid once. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkTubeJets
open Function Filter Set Metric Extraction Spec Trace Trace.Pilot TraceExtension Climb
open Boundary Boundary.Surface GapsContact GapsContact.Ascent GapsContact.Tunnel EveryPhase
open WilsonSeparatedTubeCoordinates WilsonSeparatedPositionCameras
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
    (F:Final C f S){l:Ultrafilter (ℕ×ℕ)}{H:(Bel C.book).Hierarchy}{Z:Trace.Terrace.Arch C}

theorem model (hG:G.Simple)(bliss:Bliss F l Z H){n:ℕ}(d:Fin n→ℕ){η:ℝ}(hp:0<η):
    ∃ρ:ℝ,0<ρ ∧ ∃δ∈Ioc (0:ℝ) 1,∃A:ℝ,0≤A ∧ ∃p:ℕ,
    ∀ᶠr in trail,∀x:Points n,(∀i j:Fin n,i≠j→η≤dist (x i) (x j))→
    ∀u:Points n,‖u‖≤1→∀v:(i:Fin n)→S.Field (d i),∃g:ℂ→ℂ,
      AnalyticOnNhd ℂ g (closedBall 0 ρ) ∧ (∀z∈closedBall 0 ρ,
        ‖g z‖≤A*(LogV r/δ)^p*∏i,Ascent.cost F (d i) r (v i)) ∧
      ((fun t:ℝ=>S.classMoment S d (r • (x+t • u)) v)=ᶠ[𝓝 0] fun t:ℝ=>g t):=by
  let e:Points n →L[ℝ] Full n:=embedding.comp coordinates
  obtain ⟨δ,hd,ρ,hrho,charts⟩:=WilsonMovingForkTubeRoom.original (n:=n) hp
  choose b hb rot using fun i=>WilsonPositionAllRotations.cost F hG bliss (d i)
  let R:=∏i,b i
  have Rn:0≤R:=Finset.prod_nonneg fun i _=>zero_le_one.trans (hb i)
  obtain ⟨L⟩:=almanac F
  obtain ⟨Y,-,seen⟩:=(Survey.fits L (none:Survey F)).reveals
  obtain ⟨D,X,-⟩:=(seen F.action.J F.realization.qt.induced).1.visible
  obtain ⟨A,ha,p,theater⟩:=WilsonMovingForkTubeFee.original F hG bliss L d
  refine ⟨ρ,hrho,δ,hd,A*R,mul_nonneg ha Rn,p,?_⟩
  filter_upwards [theater,eventually_all.mpr rot,self_mem_nhdsWithin (a:=0),(ge_mem_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds] with r paid rotated rp small
  intro x clear u hu v
  obtain ⟨g,σ,ordered,room⟩:=charts x clear
  let q:=view g σ x
  let a:=view g σ u
  let axis(z:ℂ):=e q+z • e a
  let w:=WilsonSeparatedPhysicalCameraChange.field F g σ v
  let film:=weather X (WilsonSeparatedTubeEnvelope.tag w) r
  have budget: (∏i,Ascent.cost F (d (σ i)) r (w i))≤R*∏i,Ascent.cost F (d i) r (v i):=by
    refine (Finset.prod_le_prod (fun _ _=>Ascent.cost_pos ..) (fun i _=>rotated (σ i) g (v (σ i)))).trans_eq ?_
    rw [Equiv.prod_comp σ (fun i=>b i*Ascent.cost F (d i) r (v i)),Finset.prod_mul_distrib]
  have len:‖e a‖≤1:=(WilsonSeparatedTubeCoordinates.isometry a).trans_le ((size g σ u).trans_le hu)
  have hits(z:ℂ)(hz:z∈closedBall 0 ρ):Room (shade (axis z)) δ:=by
    apply room
    have hz':‖z‖≤ρ:=by simpa using hz
    rw [mem_closedBall,dist_eq_norm]
    change ‖e q+z • e a-e q‖≤ρ
    rw [add_sub_cancel_left,norm_smul]
    exact (mul_le_of_le_one_right (norm_nonneg _) len).trans hz'
  obtain ⟨hol,fee⟩:=paid σ w none D X
  have ax(z:ℂ):AnalyticAt ℂ axis z:=by dsimp [axis];fun_prop
  refine ⟨fun z=>film (axis z),fun z hz=>(hol _ ((hits z hz).mem hd.1)).comp (ax z),?_,?_⟩
  · intro z hz
    have logp:0≤LogV r:=Real.log_nonneg ((one_le_inv₀ rp).mpr small)
    exact (fee δ hd _ (hits z hz)).trans ((mul_le_mul_of_nonneg_left budget
      (mul_nonneg ha (pow_nonneg (div_nonneg logp hd.1.le) _))).trans_eq (by ring))
  · have conf:x∈conf n:=by
      intro i j he
      by_contra neq
      have h:=clear i j neq;rw [he,dist_self] at h;exact hp.not_ge h
    have prior:=WilsonSeparatedPhysicalCameraChange.along F g σ v conf u rp
    apply prior.trans
    have c:Continuous (fun t:ℝ=>(coordinates (q+t • a)).2):=by fun_prop
    have origin:(coordinates (q+(0:ℝ) • a)).2∈east n:=by rw [zero_smul,add_zero];exact ordered
    filter_upwards [c.continuousAt.eventually ((open_east n).mem_nhds origin)] with t ht
    have read:=(WilsonSeparatedTubePhysicalPlane.read F L D X w rp (coordinates (q+t • a)).1
      (coordinates (q+t • a)).2 ht).symm
    rw [rebuild] at read
    calc
      _=film (e (q+t • a)):=read
      _=_:=by simp only [axis,map_add,map_smul,Complex.coe_smul]

theorem original (hG:G.Simple)(bliss:Bliss F l Z H){n:ℕ}(d:Fin n→ℕ){η:ℝ}(hp:0<η):
    ∃ρ:ℝ,0<ρ ∧ ∃δ∈Ioc (0:ℝ) 1,∃A:ℝ,0≤A ∧ ∃p:ℕ,
    ∀ᶠr in trail,∀x:Points n,(∀i j:Fin n,i≠j→η≤dist (x i) (x j))→
    ∀u:Points n,‖u‖≤1→∀v:(i:Fin n)→S.Field (d i),∀j:ℕ,
       ‖iteratedDeriv j (fun t:ℝ=>S.classMoment S d (r • (x+t • u)) v) 0‖≤
        j.factorial*(A*(LogV r/δ)^p*∏i,Ascent.cost F (d i) r (v i))/ρ^j:=by
  obtain ⟨ρ,rp,δ,hd,A,ha,p,issued⟩:=model F hG bliss d hp
  refine ⟨ρ,rp,δ,hd,A,ha,p,?_⟩
  filter_upwards [issued] with r paid x clear u hu v j
  obtain ⟨g,analytic,price,same⟩:=paid x clear u hu v
  have h0:AnalyticAt ℂ g ((0:ℝ):ℂ):=by simpa only [Complex.ofReal_zero] using analytic 0 (mem_closedBall_self rp.le)
  rw [same.iteratedDeriv_eq j,WilsonSeparatedTubeCauchy.real_jet h0 j,Complex.ofReal_zero]
  have diff:=analytic.differentiableOn
  exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j rp
    ⟨diff.mono ball_subset_closedBall,diff.continuousOn.mono closure_ball_subset_closedBall⟩
    (fun z hz=>price z (sphere_subset_closedBall hz))

end YM.Integration.WilsonMovingForkTubeJets
