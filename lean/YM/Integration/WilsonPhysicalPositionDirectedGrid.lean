import YM.Integration.WilsonPhysicalPositionDirectedReturn

/-! The directed mixed reflected detector at the actual snapped microscopic sites. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalPositionDirectedGrid
open Function Filter Set Spec Table Extraction OPE OPE.Orbits Climb Trace.Pilot PhysMS Maxwell Maxwell.Free XSpace XSpace.Normalize
open WilsonPhysicalPositionBornCandidates (operator)
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
variable (F:Final C f S)(J:ℝ→tower S)
set_option quotPrecheck false
local notation "D" => (Bel C.book).Field

open WilsonPhysicalPositionMixedRead (value)
open private dilated from YM.Integration.WilsonPhysicalPositionMixedRead

theorem moving (lead:Leading F J){I:Type*}{l:Filter I}{r t:I→ℝ}
    (hr:Tendsto r l trail){u:ℝ}(hu:0<u)(ht:Tendsto t l (𝓝 u))(pos:∀i,0<t i)
    {d:ℕ}(Z:D d→ₗ[ℂ]D d)
    (conv:∀v,Tendsto (fun i=>Frame.cocycle d J (r i) (t i) (pos i) v) l (𝓝 (Z v)))
    {n:ℕ}(near:Fin n→Bool)(p:Fin n→D d){x:Points n}(hx:x∈conf n)(grid:I→Points n)(placed:Tendsto grid l (𝓝 x)):
    Tendsto (fun i=>value F J near p (grid i) (r i) (t i)) l
      (𝓝 (WickGoal (C:=C) (d:=fun _=>d) (fun j=>if near j then p j else Z (p j)) x)):=by
  let c i:=Frame.cocycle d J (r i) (t i) (pos i)
  let b i j:=if near j then p j else c i (p j)
  let v j:=if near j then p j else Z (p j)
  have columns(j:Fin n):Tendsto (fun i=>b i j) l (𝓝 (v j)):=by
    cases h:near j with
    | false=>simpa only [b,v,h,Bool.false_eq_true,if_false,c] using conv (p j)
    | true=>simpa only [b,v,h,if_true] using (tendsto_const_nhds: Tendsto (fun _:I=>p j) l (𝓝 (p j)))
  let a i j:=Pert.Scale.gear C.labels d (t i) (b i j)
  have read:=WilsonPhysicalPositionBornTransition.several F J lead hr (ht.smul placed)
    (Work.A05.smul_conf hu hx) (fun j=>dilated ht (columns j))
  have same(i:I):measured F none (J (r i)) (d:=fun _=>d) (a i) (r i) (t i • grid i)=value F J near p (grid i) (r i) (t i):=by
    unfold measured WilsonPhysicalPositionMixedRead.value
    rw [smul_smul,mul_comm (r i) (t i)]
    congr 1
    funext j
    cases h:near j with
    | false=>
      dsimp only [a,b,c]
      simp only [h,Bool.false_eq_true,if_false]
      exact Frame.cocycle_value d J (p j) (t i) (r i) (pos i)
    | true=>simp only [a,b,h,if_true]
  have calibrated:=Pert.Scale.points_equ (F:=C.labels) hx v hu.ne'
  change WickGoal (C:=C) (d:=fun _=>d) (fun j=>Pert.Scale.gear C.labels d u (v j)) (u • x)=
    WickGoal (C:=C) (d:=fun _=>d) v x at calibrated
  rw [←calibrated]
  exact read.congr same

theorem original (lead:Leading F J){I:Type*}{l:Filter I}{r t:I→ℝ}
    (hr:Tendsto r l trail){u:ℝ}(hu:0<u)(ht:Tendsto t l (𝓝 u))(pos:∀i,0<t i)
    {d:ℕ}(Z:D d→ₗ[ℂ]D d)(conv:∀v,Tendsto (fun i=>Frame.cocycle d J (r i) (t i) (pos i) v) l (𝓝 (Z v)))
    (v:D d)(grid:I→Points 2)(placed:Tendsto grid l (𝓝 WilsonPhysicalPositionReflectedReturn.sites)):
    Tendsto (fun i=>(∑s:Signed,(value F J (fun j:Fin 2=>decide (j=0)) (WilsonPhysicalPositionReflectedReturn.ports v s) (grid i) (r i) (t i)).re)-
      WilsonPhysicalPositionDirectedReturn.cross F J v (r i) (t i)) l (𝓝 0):=by
  let port:=WilsonPhysicalPositionReflectedReturn.ports v
  have zero(s:Signed):Tendsto (fun i=>(value F J (fun j:Fin 2=>decide (j=0)) (port s) (grid i) (r i) (t i)).re-
      (value F J (fun j:Fin 2=>decide (j=0)) (port s) WilsonPhysicalPositionReflectedReturn.sites (r i) (t i)).re) l (𝓝 0):=by
    let h:=moving F J lead hr hu ht pos Z conv (fun j:Fin 2=>decide (j=0)) (port s) WilsonPhysicalPositionReflectedReturn.clear grid placed
    let h₀:=WilsonPhysicalPositionMixedRead.limit F J lead hr hu ht pos Z conv (fun j:Fin 2=>decide (j=0)) (port s) WilsonPhysicalPositionReflectedReturn.clear
    simpa only [Function.comp_apply,sub_self] using (Complex.continuous_re.continuousAt.tendsto.comp h).sub
      (Complex.continuous_re.continuousAt.tendsto.comp h₀)
  simpa only [Finset.sum_sub_distrib,Finset.sum_const_zero,WilsonPhysicalPositionDirectedReturn.cross,port]
    using tendsto_finsetSum Finset.univ (fun s _=>zero s)

end YM.Integration.WilsonPhysicalPositionDirectedGrid
end
