import YM.Integration.WilsonOriginalPublicNodalEntry

/-! A finite signed panel of enrolled original nodes at a common public vector.
Every declared independent board is evaluated at its own full set of sites. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 700000
namespace YM.Integration.WilsonOriginalPublicNodalNodes
open Finset Lattice Wilson RG Source Labels Marker QuadraticLocal.Affinity PhysicalNext.Repeat.Legato
open Pert.Asymptotics RegulatorIR.FVAAlt2
open XSpace XSpace.Normalize XSpace.Rose XSpace.Cirrus
open WilsonOriginalPublicPivotReflected (evaluated board sampled)
open WilsonOriginalPublicNodalEntry (dose enter Issued balance)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)(W:Initialize G){n:ℕ}(d:Fin n→ℕ){N per K u:ℕ}
    (v:∀i,R.family.label (d i))(z:Fin n→ℂ)
    (x:Wallet (WilsonOriginalAlternativeFiniteSource.disks (V:=Fin n)))(s:(Stock.census (Fin n)).Mode)
variable {J:Type}[Fintype J](nodes:J→Sample n)(μ:J→ℂ)(o:J→Fin n→Site (R.family.side K per))
    (position:∀j,∀i:s.val,wrap (R.family.side K per) ((nodes j).layout i)=o j i)
    (high:K≤N)(ear:u≤K)(Y:J→ Config G (R.family.side N per)→ℂ)(fee:J→ℝ)
    (bought:∀j,Issued R d (o j) v z x s high ear (Y j) (fee j))
local notation "g₀" => regulatorRun R.family N per K
local notation "chart" => dose R d (N:=N) (K:=K) (per:=per) v z x
local notation "phase" j:max => WilsonOriginalTwoFlatGridScaling.gap R N per u (ear.trans high) (Y j)

def primitive (q:ℕ)(j:J):ℂ:=balance R d (N:=N) (per:=per) v z x s
  (nodes j).layout (nodes j).F.p (W.tree (nodes j).F.p) q ear 1

include position bought in
theorem original (q:ℕ):
    let physical:=∑j,μ j*R.family.omega N per (Y j)
    let filed:=sampled R W d chart nodes μ s.val q g₀
    let signed:=∑j,μ j*primitive R W d (N:=N) (per:=per) v z x s nodes ear q j
    physical-filed-signed=∑j,μ j*(phase j+enter R d (o j) v z x s high ear (Y j)) ∧
      ‖physical-filed-signed‖≤∑j,‖μ j‖*(‖phase j‖+fee j):=by
  intro physical filed signed
  have one(j:J):
      R.family.omega N per (Y j)-evaluated q g₀ (board R W d chart (nodes j) s.val)-
        primitive R W d (N:=N) (per:=per) v z x s nodes ear q j=
        phase j+enter R d (o j) v z x s high ear (Y j) ∧
      ‖R.family.omega N per (Y j)-evaluated q g₀ (board R W d chart (nodes j) s.val)-
        primitive R W d (N:=N) (per:=per) v z x s nodes ear q j‖≤‖phase j‖+fee j:=
    bought j (nodes j).layout (position j) (nodes j).F.p (W.tree (nodes j).F.p) q
  have split:physical-filed-signed=∑j,μ j*(R.family.omega N per (Y j)-
      evaluated q g₀ (board R W d chart (nodes j) s.val)-primitive R W d (N:=N) (per:=per) v z x s nodes ear q j):=by
    dsimp only [physical,filed,signed,sampled]
    simp only [mul_sub,Finset.sum_sub_distrib]
  rw [split]
  constructor
  · exact sum_congr rfl fun j _=>congrArg (μ j*·) (one j).1
  · refine (norm_sum_le ..).trans (sum_le_sum fun j _=>?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (one j).2 (norm_nonneg _)

include position bought in
theorem priced (q:ℕ)(A B:ℝ)(physicalPhase:∀j,‖phase j‖≤A)(localFee:∀j,fee j≤B):
    ‖(∑j,μ j*R.family.omega N per (Y j))-sampled R W d chart nodes μ s.val q g₀‖≤
      (∑j,‖μ j‖)*(A+B)+‖∑j,μ j*primitive R W d (N:=N) (per:=per) v z x s nodes ear q j‖:=by
  have h:=(original R W d v z x s nodes μ o position high ear Y fee bought q).2
  have cap:(∑j,‖μ j‖*(‖phase j‖+fee j))≤(∑j,‖μ j‖)*(A+B):=by
    rw [Finset.sum_mul]
    exact sum_le_sum fun j _=>mul_le_mul_of_nonneg_left (add_le_add (physicalPhase j) (localFee j)) (norm_nonneg _)
  exact (norm_le_norm_sub_add ..).trans (add_le_add (h.trans cap) le_rfl)

end YM.Integration.WilsonOriginalPublicNodalNodes
end
