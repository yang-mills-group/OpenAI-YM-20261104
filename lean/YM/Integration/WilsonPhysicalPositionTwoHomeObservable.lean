import YM.Integration.WilsonPhysicalPositionRealBranchPanel

/-! The original two-home signed scalar on both actual fields. Its cluster
read on the compensated dilation is computed without a hypothesis
identifying either field with a formally surveyed finite-cutoff source. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalPositionTwoHomeObservable
open Function Filter Set Spec Table Extraction OPE OPE.Orbits Climb Trace.Pilot PhysMS Maxwell Maxwell.Free XSpace XSpace.Normalize
open WilsonPhysicalPositionBornCandidates (operator)
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
variable (F:Final C f S)(J:ℝ→tower S)
set_option quotPrecheck false
local notation "D" => (Bel C.book).Field

def heard {d n:ℕ}(p:Fin n→D d)(x:Points n)(r t:ℝ):ℂ:=
  S.classMoment (spectator F none) (fun _=>d) ((t*r) • x) (fun j=>
    J r d (Pert.Scale.gear C.labels d t (p j))-J (t*r) d (p j))

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

theorem limit (lead:Leading F J){I:Type*}{l:Filter I}{r t:I→ℝ}
    (hr:Tendsto r l trail){u:ℝ}(hu:0<u)(ht:Tendsto t l (𝓝 u))(pos:∀i,0<t i)
    {d:ℕ}(Z:D d→ₗ[ℂ]D d)
    (conv:∀v,Tendsto (fun i=>Frame.cocycle d J (r i) (t i) (pos i) v) l (𝓝 (Z v)))
    {n:ℕ}(p:Fin n→D d){x:Points n}(hx:x∈conf n):
    Tendsto (fun i=>heard F J p x (r i) (t i)) l
      (𝓝 (WickGoal (C:=C) (d:=fun _=>d) (fun j=>p j-Z (p j)) x)):=by
  let z i:=Frame.cocycle d J (r i) (t i) (pos i)
  let a i j:=Pert.Scale.gear C.labels d (t i) (p j-z i (p j))
  have hv(j:Fin n):Tendsto (fun i=>a i j) l (𝓝 (Pert.Scale.gear C.labels d u (p j-Z (p j)))):=
    dilated ht (tendsto_const_nhds.sub (conv (p j)))
  have read:=WilsonPhysicalPositionBornTransition.several F J lead hr (ht.smul (tendsto_const_nhds (x:=x)))
    (Work.A05.smul_conf hu hx) hv
  have same(i:I):measured F none (J (r i)) (d:=fun _=>d) (a i) (r i) (t i • x)=heard F J p x (r i) (t i):=by
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

end YM.Integration.WilsonPhysicalPositionTwoHomeObservable
end
