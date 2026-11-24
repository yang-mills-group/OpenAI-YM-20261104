import YM.Integration.WilsonPhysicalPositionReflectedReturn

/-! The same reflected branch detector at the actual snapped microscopic sites. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalPositionGridReturn
open Function Filter Set Spec Table Extraction OPE OPE.Orbits Climb Trace.Pilot PhysMS Maxwell Maxwell.Free XSpace XSpace.Normalize
open WilsonPhysicalPositionBornCandidates (operator)
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
variable (F:Final C f S)(J:ℝ→tower S)
set_option quotPrecheck false
local notation "D" => (Bel C.book).Field

open WilsonPhysicalPositionTwoHomeObservable (heard)
private theorem dilated {I:Type*}{l:Filter I}{d:ℕ}{t:I→ℝ}{s:ℝ}
    (ht:Tendsto t l (𝓝 s)){v:I→D d}{z:D d}(hv:Tendsto v l (𝓝 z)):
    Tendsto (fun i=>Pert.Scale.gear C.labels d (t i) (v i)) l (𝓝 (Pert.Scale.gear C.labels d s z)):=by
  apply Dash.arcing (Dash.fit_plane (fun i=>Pert.Scale.gear C.labels d (t i)) (Pert.Scale.gear C.labels d s) ?_) hv
  intro u
  have continuous:Continuous (fun a:ℝ=>Pert.Scale.gear C.labels d a u):=by
    let B:=Extra.FD.recorded C.labels d
    conv => arg 1; ext a; rw [← B.b.sum_repr u,map_sum]
    simp_rw [map_smul,Pert.Scale.rare]
    fun_prop
  exact (continuous.tendsto _).comp ht

theorem moving (lead:Leading F J){I:Type*}{l:Filter I}{r t:I→ℝ}
    (hr:Tendsto r l trail){u:ℝ}(hu:0<u)(ht:Tendsto t l (𝓝 u))(pos:∀i,0<t i)
    {d:ℕ}(Z:D d→ₗ[ℂ]D d)
    (conv:∀v,Tendsto (fun i=>Frame.cocycle d J (r i) (t i) (pos i) v) l (𝓝 (Z v)))
    {n:ℕ}(p:Fin n→D d){x:Points n}(hx:x∈conf n)(grid:I→Points n)(placed:Tendsto grid l (𝓝 x)):
    Tendsto (fun i=>heard F J p (grid i) (r i) (t i)) l
      (𝓝 (WickGoal (C:=C) (d:=fun _=>d) (fun j=>p j-Z (p j)) x)):=by
  let z i:=Frame.cocycle d J (r i) (t i) (pos i)
  let a i j:=Pert.Scale.gear C.labels d (t i) (p j-z i (p j))
  have hv(j:Fin n):Tendsto (fun i=>a i j) l (𝓝 (Pert.Scale.gear C.labels d u (p j-Z (p j)))):=
    dilated ht (tendsto_const_nhds.sub (conv (p j)))
  have read:=WilsonPhysicalPositionBornTransition.several F J lead hr (ht.smul placed)
    (Work.A05.smul_conf hu hx) hv
  have same(i:I):measured F none (J (r i)) (d:=fun _=>d) (a i) (r i) (t i • grid i)=heard F J p (grid i) (r i) (t i):=by
    unfold heard measured
    rw [smul_smul,mul_comm (r i) (t i)]
    congr 1
    funext j
    dsimp only [a,z]
    rw [map_sub,map_sub,Frame.cocycle_value]
  have calibrated:=Pert.Scale.points_equ (F:=C.labels) hx (fun j=>p j-Z (p j)) hu.ne'
  change WickGoal (C:=C) (d:=fun _=>d) (fun j=>Pert.Scale.gear C.labels d u (p j-Z (p j))) (u • x)=
    WickGoal (C:=C) (d:=fun _=>d) (fun j=>p j-Z (p j)) x at calibrated
  rw [←calibrated]
  exact read.congr same

theorem original (lead:Leading F J){I:Type*}{l:Filter I}{r t:I→ℝ}
    (hr:Tendsto r l trail){u:ℝ}(hu:0<u)(ht:Tendsto t l (𝓝 u))(pos:∀i,0<t i)
    {d:ℕ}(Z:D d→ₗ[ℂ]D d)(conv:∀v,Tendsto (fun i=>Frame.cocycle d J (r i) (t i) (pos i) v) l (𝓝 (Z v)))
    (v:D d)(grid:I→Points 2)(placed:Tendsto grid l (𝓝 WilsonPhysicalPositionReflectedReturn.sites)):
    Tendsto (fun i=>(∑s:Signed,(heard F J (WilsonPhysicalPositionReflectedReturn.ports v s) (grid i) (r i) (t i)).re)-
      WilsonPhysicalPositionReflectedReturn.reading F J v (r i) (t i)) l (𝓝 0):=by
  let port:=WilsonPhysicalPositionReflectedReturn.ports v
  have zero(s:Signed):Tendsto (fun i=>(heard F J (port s) (grid i) (r i) (t i)).re-
      (heard F J (port s) WilsonPhysicalPositionReflectedReturn.sites (r i) (t i)).re) l (𝓝 0):=by
    let h:=moving F J lead hr hu ht pos Z conv (port s) WilsonPhysicalPositionReflectedReturn.clear grid placed
    let h₀:=WilsonPhysicalPositionTwoHomeObservable.limit F J lead hr hu ht pos Z conv (port s) WilsonPhysicalPositionReflectedReturn.clear
    simpa only [Function.comp_apply,sub_self] using (Complex.continuous_re.continuousAt.tendsto.comp h).sub
      (Complex.continuous_re.continuousAt.tendsto.comp h₀)
  simpa only [Finset.sum_sub_distrib,Finset.sum_const_zero,WilsonPhysicalPositionReflectedReturn.reading,port]
    using tendsto_finsetSum Finset.univ (fun s _=>zero s)

end YM.Integration.WilsonPhysicalPositionGridReturn
end
