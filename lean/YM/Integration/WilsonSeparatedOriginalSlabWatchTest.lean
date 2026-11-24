import YM.Integration.WilsonSeparatedOriginalSlabWatchRoom

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalSlabWatchTest
open Set Function MeasureTheory RG05Readout RG05Readout.Pulse RG05Readout.Native
open WilsonSeparatedOriginalSlabWatchMean WilsonSeparatedOriginalSlabWatchRoom
open scoped Topology ContDiff Classical
variable {n:ℕ}

def area (A:Set (Cloud (Fin n))):Set (Points n):=points '' space A

theorem closed (A:Set (Cloud (Fin n)))(bound:IsCompact A):IsCompact (area A):=(WilsonSeparatedOriginalSlabWatchRoom.compact bound).image (PiLp.continuous_toLp 2 _)

theorem located {θ:ℝ}(ht:θ∈Icc (0:ℝ) 1)(A:Set (Cloud (Fin n)))(bound:IsCompact A)
    (Ψ:Wave (Fin n))(filed:tsupport Ψ.val⊆A)(g:Body):
    tsupport (fun y:Points n=>(wave θ Ψ g).val y.ofLp)⊆area A:=by
  apply closure_minimal _ (closed A bound).isClosed
  intro y hy;exact ⟨y.ofLp,WilsonSeparatedOriginalSlabWatchRoom.original θ ht Ψ g A bound filed (subset_tsupport _ hy),rfl⟩

theorem safe (A:Set (Cloud (Fin n))){η M:ℝ}(pos:0<η)
    (apart:∀x∈A,∀i j:Fin n,i≠j→η≤‖x i-x j‖)(size:∀x∈A,∀i,‖x i‖≤M):area A⊆conf n:=by
  rintro _ ⟨x,hx,rfl⟩ i j hij;by_contra ne
  have price:η≤‖x i-x j‖:=(housing A apart size x hx).1 i j ne
  rw [show x i=x j from hij,sub_self,norm_zero] at price;exact (not_le_of_gt pos) price

def physical {θ:ℝ}(ht:θ∈Icc (0:ℝ) 1)(A:Set (Cloud (Fin n)))(bound:IsCompact A)
    (Ψ:Wave (Fin n))(filed:tsupport Ψ.val⊆A)(g:Body){η M:ℝ}(pos:0<η)
    (apart:∀x∈A,∀i j:Fin n,i≠j→η≤‖x i-x j‖)(size:∀x∈A,∀i,‖x i‖≤M):Test n:=by
  let φ:=fun y:Points n=>(wave θ Ψ g).val y.ofLp
  have supp:tsupport φ⊆area A:=located ht A bound Ψ filed g
  refine ⟨φ,(show ContDiff ℝ ∞ (wave θ Ψ g).val from (wave θ Ψ g).property).comp (PiLp.continuousLinearEquiv 2 ℝ (fun _:Fin n=>E4)).contDiff,
    (closed A bound).of_isClosed_subset (isClosed_tsupport _) supp,?_⟩
  exact supp.trans (safe A pos apart size)

@[simp] theorem value {θ:ℝ}(ht:θ∈Icc (0:ℝ) 1)(A:Set (Cloud (Fin n)))(bound:IsCompact A)
    (Ψ:Wave (Fin n))(filed:tsupport Ψ.val⊆A)(g:Body){η M:ℝ}(pos:0<η)
    (apart:∀x∈A,∀i j:Fin n,i≠j→η≤‖x i-x j‖)(size:∀x∈A,∀i,‖x i‖≤M)(y:Points n):
    physical ht A bound Ψ filed g pos apart size y=∫z in Native.box,g.val z*Ψ.val (y.ofLp+delta θ z):=rfl

end YM.Integration.WilsonSeparatedOriginalSlabWatchTest
