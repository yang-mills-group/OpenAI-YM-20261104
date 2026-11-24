import YM.Integration.WilsonPhysicalPositionDiscreteBranches
import YM.Integration.WilsonPhysicalPositionHomeStability
import YM.PhysMS.Frame.Step

/-! Every converging bounded-ratio transition of the genuine physical fields
preserves every separated free moment. Both radii are measured on the same
physical construction with the complete field, including the unit. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalPositionBornTransition
open Function Filter Set Spec Table Extraction OPE OPE.Orbits Climb Trace.Pilot PhysMS Maxwell Maxwell.Free XSpace XSpace.Normalize
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
variable (F:Final C f S)(J:ℝ→tower S)
set_option quotPrecheck false
local notation "D" => (Bel C.book).Field

private theorem finite_rows {U:Type}[NormedAddCommGroup U][NormedSpace ℂ U][FiniteDimensional ℂ U]
    {I:Type*}{l:Filter I}{n:ℕ}(A:I→MultilinearMap ℂ (fun _:Fin n=>U) ℂ)
    (B:MultilinearMap ℂ (fun _:Fin n=>U) ℂ)
    (rows:∀w,Tendsto (fun i=>A i w) l (𝓝 (B w)))
    {a:I→Fin n→U}{b:Fin n→U}(arms:∀j,Tendsto (fun i=>a i j) l (𝓝 (b j))):
    Tendsto (fun i=>A i (a i)) l (𝓝 (B b)):=by
  let P:=Module.finBasis ℂ U
  let K:=Fin (Module.finrank ℂ U)
  have expand (X:MultilinearMap ℂ (fun _:Fin n=>U) ℂ)(v:Fin n→U):
      X v=∑z:Fin n→K,(∏j,P.coord (z j) (v j)) • X (fun j=>P (z j)):=by
    have e:=X.map_sum (fun j (k:K)=>P.repr (v j) k • P k)
    have repr (j:Fin n):(∑k:K,P.repr (v j) k • P k)=v j:=P.sum_repr _
    rw [funext repr] at e
    rw [e]
    exact Finset.sum_congr rfl fun z _=>X.map_smul_univ _ _
  have co(z:Fin n→K):Tendsto (fun i=>∏j,P.coord (z j) (a i j)) l (𝓝 (∏j,P.coord (z j) (b j))):=by
    apply tendsto_finsetProd
    intro j _
    exact ((P.coord (z j)).continuous_of_finiteDimensional.tendsto _).comp (arms j)
  simpa only [←expand] using (tendsto_finsetSum Finset.univ
    fun (z:Fin n→K) _=>(co z).smul (rows (fun j=>P (z j))))

theorem several (lead:Leading F J){I:Type*}{l:Filter I}{n d:ℕ}
    {r:I→ℝ}(hr:Tendsto r l trail){x:I→Points n}{y:Points n}(hx:Tendsto x l (𝓝 y))(hy:y∈conf n)
    {a:I→Fin n→D d}{b:Fin n→D d}(arms:∀j,Tendsto (fun i=>a i j) l (𝓝 (b j))):
    Tendsto (fun i=>measured F none (J (r i)) (d:=fun _=>d) (a i) (r i) (x i)) l
      (𝓝 (WickGoal (C:=C) (d:=fun _=>d) b y)):=by
  let A i:MultilinearMap ℂ (fun _:Fin n=>D d) ℂ:=
    (S.classMoment (spectator F none) (fun _=>d) (r i • x i)).compLinearMap (fun _=>(J (r i) d).toLinearMap)
  exact finite_rows A ((Bel C.book).classMoment (Bel C.book) (fun _=>d) y)
    (fun v=>leading_at F lead (d:=fun _=>d) v hr hx hy) arms

private theorem engine {I:Type*}{l:Filter I}{d:ℕ}{t:I→ℝ}{s:ℝ}
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

theorem invariant (lead:Leading F J){I:Type*}{l:Filter I}[NeBot l]{r t:I→ℝ}
    (hr:Tendsto r l trail){u:ℝ}(hu:0<u)(ht:Tendsto t l (𝓝 u))(pos:∀i,0<t i)
    {d:ℕ}(B:D d→ₗ[ℂ] D d)
    (converges:∀v,Tendsto (fun i=>Frame.cocycle d J (r i) (t i) (pos i) v) l (𝓝 (B v)))
    {n:ℕ}(p:Fin n→D d){x:Points n}(hx:x∈conf n):
    WickGoal (C:=C) (d:=fun _=>d) (fun j=>B (p j)) x=WickGoal (C:=C) (d:=fun _=>d) p x:=by
  let c i:=Frame.cocycle d J (r i) (t i) (pos i)
  let v i j:=Pert.Scale.gear C.labels d (t i) (c i (p j))
  have h1:=several F J lead hr (ht.smul (tendsto_const_nhds (x:=x))) (Work.A05.smul_conf hu hx)
    (fun j=>engine ht (converges (p j)))
  have radii:Tendsto (fun i=>t i*r i) l trail:=by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,?_⟩
    · simpa only [mul_zero] using ht.mul (hr.mono_right nhdsWithin_le_nhds)
    filter_upwards [hr.eventually self_mem_nhdsWithin] with i hi using mul_pos (pos i) hi
  have h2:=leading_at F lead (d:=fun _=>d) p radii (tendsto_const_nhds (x:=x)) hx
  have link i:measured F none (J (r i)) (d:=fun _=>d) (v i) (r i) (t i • x)=
      measured F none (J (t i*r i)) (d:=fun _=>d) p (t i*r i) x:=by
    unfold measured
    rw [smul_smul,mul_comm (r i) (t i)]
    congr 1
    funext j
    exact Frame.cocycle_value d J (p j) (t i) (r i) (pos i)
  exact (Pert.Scale.points_equ (F:=C.labels) hx (fun j=>B (p j)) hu.ne').symm.trans
    (tendsto_nhds_unique (h1.congr link) h2)

def present {d:ℕ}(T:FieldEnd G d):D d→ₗ[ℂ] D d:=
  (fields C.labels d).symm.toLinearMap ∘ₗ T ∘ₗ (fields C.labels d).toLinearMap

theorem original (lead:Leading F J){I:Type*}{l:Filter I}[NeBot l]{r t:I→ℝ}
    (hr:Tendsto r l trail){u:ℝ}(hu:0<u)(ht:Tendsto t l (𝓝 u))(pos:∀i,0<t i)
    {d:ℕ}(b:MoveSpace G d)
    (converges:∀v,Tendsto (fun i=>Frame.cocycle d J (r i) (t i) (pos i) v) l
      (𝓝 (present (C:=C) (WilsonPhysicalPositionDiscreteBranches.field b) v))):
    WilsonPhysicalPositionDiscreteBranches.preserves b:=by
  unfold WilsonPhysicalPositionDiscreteBranches.preserves
  funext n
  apply LinearMap.ext
  intro test
  apply MultilinearMap.ext
  intro p
  apply test.apply_eq
  intro x hx
  have h:=invariant F J lead hr hu ht pos _ converges (fun j=>(fields C.labels d).symm (p j)) hx
  simpa only [present,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply,
    WilsonPositionPrescribedScreen.zero] using h

end YM.Integration.WilsonPhysicalPositionBornTransition
end
