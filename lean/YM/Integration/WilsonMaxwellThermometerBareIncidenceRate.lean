import YM.Integration.WilsonMaxwellThermometerReflectedFirstPrice
import YM.XSpace.BareProfiles

/-! A linear-spacing price for the full pure bare column on each separated
tuple, including moving finite field doses.  The common leading frame is
retained on both sides before applying a first-incidence variation. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerBareIncidenceRate
open Filter Set Finset Lattice Wilson Maxwell Maxwell.Free XSpace XSpace.Cirrus
open XSpace.Normalize XSpace.Structure1 XSpace.Rose XSpace.Photo XSpace.Retirement
open scoped Topology BigOperators Classical
variable {G:Gauge}{n:ℕ}(W:Initialize G)(d:ℕ)

/-- All homogeneous weights of every actual bare leg are included, without
moving the test to a fresh Gaussian after the reporting boundary. -/
theorem bare (p:Tags G d n){K:Set (Points n)}(compact:IsCompact K)(apart:K⊆conf n):
    ∃C:ℝ,0≤C ∧ ∀ᶠ M in Front,∀u:pack n,∀c∈M.Box,M.rel u c∈K →
      ‖live W d ⟨M,u,c⟩ 0 p-scene (M.rel u c) d p‖≤C*M.spacing:=by
  let I:=Fin n→Fin (d+1)
  let grade (r:I)(j:Fin n):ℕ:=(r j).val
  let projected (r:I)(j:Fin n):On.Grade G (grade r j):=part d (r j) (p j)
  choose C hp fee using fun r:I=>Mesh.uniform W (grade r) frontier K compact apart (projected r)
  refine ⟨∑r,C r,sum_nonneg (fun r _=>(hp r).le),?_⟩
  filter_upwards [eventually_all.mpr fee] with M ready
  intro u c hc good
  rw [lite,calls (scene (M.rel u c) d) p,←sum_sub_distrib]
  calc
    _ ≤ ∑r:I,‖M.note W (grade r) (projected r) (wrap M.p.side ∘ u)
      -Mesh.MaxwellPoint (grade r) (projected r) (M.rel u c)‖:=norm_sum_le ..
    _ ≤ ∑r:I,C r*M.spacing:=sum_le_sum (fun r _=>ready r u c hc good)
    _ = _:=by rw [sum_mul]

def assembled {I:Fin n→Type}[∀j,Fintype (I j)](f:∀j,I j→Sec G d)
    (v:∀j,I j→ℂ):Tags G d n:=fun j=>∑i,v j i • f j i

theorem moving {I:Fin n→Type}[∀j,Fintype (I j)](f:∀j,I j→Sec G d)
    {K:Set (Points n)}(compact:IsCompact K)(apart:K⊆conf n):
    ∃C:ℝ,0≤C ∧ ∀ᶠ M in Front,∀u:pack n,∀c∈M.Box,M.rel u c∈K →
    ∀v:∀j,I j→ℂ,‖live W d ⟨M,u,c⟩ 0 (assembled d f v)-scene (M.rel u c) d (assembled d f v)‖≤
      (C*M.spacing)*∏j,∑i,‖v j i‖:=by
  choose c pos good using fun b:∀j,I j=>bare W d (fun j=>f j (b j)) compact apart
  let C:=∑b,c b
  have hC:0≤C:=sum_nonneg (fun b _=>pos b)
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_all.mpr good] with M fee
  intro u o ho hk v
  let A:=live W d ⟨M,u,o⟩ 0-scene (M.rel u o) d
  change ‖A (fun j=>∑i,v j i •f j i)‖≤_
  rw [MultilinearMap.map_sum_finset]
  calc
    _≤∑b:∀j,I j,‖A (fun j=>v j (b j) • f j (b j))‖:=norm_sum_le ..
    _≤∑b:∀j,I j,(C*M.spacing)*∏j,‖v j (b j)‖:=by
      apply sum_le_sum
      intro b _
      rw [A.map_smul_univ,norm_smul,norm_prod,mul_comm]
      apply mul_le_mul_of_nonneg_right _ (prod_nonneg fun _ _=>norm_nonneg _)
      have cb:c b≤C:=single_le_sum (f:=c) (fun j _=>pos j) (mem_univ b)
      exact (fee b u o ho hk).trans (mul_le_mul_of_nonneg_right cb M.positive.le)
    _= _:=by rw [←mul_sum,Fintype.prod_sum]

end YM.Integration.WilsonMaxwellThermometerBareIncidenceRate
