import YM.Integration.WilsonWindowReportingPace
import YM.RG16.Unmasked.Pace

/-! The forward ultraviolet and backward far stops on the actual varying
Wilson mesh. They are fixed from the selected calendar before any field,
test, phase or physical period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorMeshStops
open Function Filter Set Real Lattice RG RG16
open scoped Topology Classical
variable {G:Gauge} (C:Family G)
local notation "S₀" => C.S.scale
local notation "Λ₀" => RG16.Lambda C.path.levels
local notation "β₀" => C.path.levels.clock.hatBeta

private theorem passes (x:ℝ) : ∃ j:ℕ,x≤S₀ j :=
  (C.S.divergent.eventually_ge_atTop x).exists

def crossing (x:ℝ) : ℕ:=Nat.find (passes C x)

private theorem first (x:ℝ) (hx:0<x) :
    ∃ j:ℕ, crossing C x=j+1 ∧ S₀ j<x ∧ x≤S₀ (j+1) := by
  have reached : x≤S₀ (crossing C x):=Nat.find_spec (passes C x)
  have positive : 0<crossing C x := by
    by_contra! hz
    rw [show crossing C x=0 by omega, C.S.scale_zero] at reached
    linarith
  refine ⟨crossing C x-1,by omega,?_,?_⟩
  · exact lt_of_not_ge (Nat.find_min (passes C x) (show crossing C x-1<crossing C x by omega))
  · simpa only [show crossing C x-1+1=crossing C x by omega] using reached

private theorem fiscal (hG:G.Simple) (c:ℝ) :
    ∀ᶠ k:ℕ in atTop,2*G.slopeConstant*(Λ₀ k)^c≤β₀ k := by
  have small:=((isLittleO_rpow_exp_atTop c).const_mul_left (2*G.slopeConstant)).bound
    (Real.exp_pos (-2))
  filter_upwards [(RG16.Literal.lambda_leads C hG).eventually small] with k hk
  have h : |2*G.slopeConstant*(Λ₀ k)^c|≤exp (-2)*|exp (Λ₀ k)| := by
    simpa only [Real.norm_eq_abs] using hk
  rw [abs_of_pos (exp_pos _),←exp_add] at h
  have hb : 0<β₀ k := zero_lt_one.trans (C.path.levels.fits.delayed k)
  have same : -2+Λ₀ k=log (β₀ k) := by unfold RG16.Lambda; ring
  rw [same,exp_log hb] at h
  exact (le_abs_self _).trans h

private theorem jump (slow:∀ m,((C.S.block m).val:ℝ)≤log (Λ₀ m)) (j:ℕ) :
    S₀ (j+1)≤S₀ j+log (log (Λ₀ j)) := by
  rw [C.S.scale_succ]
  exact add_le_add_right (log_le_log (by exact_mod_cast (C.S.block j).pos) (slow j)) _

def ultraviolet (c:ℝ) (k:ℕ) := crossing C (S₀ k+(Λ₀ k)^c)
def far (c:ℝ) (k:ℕ) := crossing C (S₀ k-(Λ₀ k)^c)

theorem ultraviolet_window (hG:G.Simple)
    (slow:∀ m,((C.S.block m).val:ℝ)≤log (Λ₀ m)) (c:ℝ) :
    ∀ᶠ k:ℕ in atTop,k<ultraviolet C c k ∧
      (Λ₀ k)^c≤S₀ (ultraviolet C c k)-S₀ k ∧
      S₀ (ultraviolet C c k)-S₀ k≤(Λ₀ k)^c+log (log (Λ₀ k+log 2)) := by
  filter_upwards [fiscal C hG c,C.S.divergent.eventually_ge_atTop 0] with k hk hs
  let v:ℝ:=(Λ₀ k)^c
  have hv:0<v:=rpow_pos_of_pos (RG16.Literal.lambda_pos C k) c
  obtain ⟨j,eq,below,above⟩:=first C (S₀ k+v) (by linarith)
  change k<crossing C (S₀ k+v) ∧ _
  change k<crossing C (S₀ k+v) ∧ v≤S₀ (crossing C (S₀ k+v))-S₀ k ∧
    S₀ (crossing C (S₀ k+v))-S₀ k≤v+log (log (Λ₀ k+log 2))
  rw [eq]
  have slope:=Gauge.slopeConstant_pos hG
  have small : G.slopeConstant*v≤β₀ k := by
    change 2*G.slopeConstant*v≤_ at hk
    linarith [mul_pos slope hv]
  have beta : β₀ j≤β₀ k+G.slopeConstant*v := by
    change _+G.slopeConstant*S₀ j≤(_+G.slopeConstant*S₀ k)+_
    linarith [mul_le_mul_of_nonneg_left below.le slope.le]
  have hbk:=zero_lt_one.trans (C.path.levels.fits.delayed k)
  have hj:=RG16.Literal.lambda_up C j
  have bound : Λ₀ j≤Λ₀ k+log 2 := by
    have hlog:=log_le_log (zero_lt_one.trans (C.path.levels.fits.delayed j))
      (show β₀ j≤β₀ k*2 by linarith)
    rw [log_mul hbk.ne' (by norm_num : (2:ℝ)≠0)] at hlog
    unfold RG16.Lambda
    linarith
  have hh:=log_le_log (log_pos (by linarith : 1<Λ₀ j))
    (log_le_log (RG16.Literal.lambda_pos C j) bound)
  refine ⟨?_,by linarith,?_⟩
  · by_contra! bad
    have wk:= (OPE.scale_mono C.S).monotone bad
    linarith
  · linarith [jump C slow j]

theorem far_window (hG:G.Simple)
    (slow:∀ m,((C.S.block m).val:ℝ)≤log (Λ₀ m)) (c:ℝ) :
    ∀ᶠ k:ℕ in atTop, far C c k≤k ∧
      (Λ₀ k)^c-log (log (Λ₀ k)) ≤ S₀ k-S₀ (far C c k) ∧
      S₀ k-S₀ (far C c k)≤(Λ₀ k)^c := by
  have slope:=Gauge.slopeConstant_pos hG
  have large:=C.S.divergent.eventually_gt_atTop (C.path.levels.clock.bar/G.slopeConstant)
  filter_upwards [fiscal C hG c,large] with k hk hl
  let v:ℝ:=(Λ₀ k)^c
  have hv:0<v:=rpow_pos_of_pos (RG16.Literal.lambda_pos C k) c
  have hs : v<S₀ k := by
    have hb:= (div_lt_iff₀ slope).mp hl
    change 2*G.slopeConstant*v≤_+G.slopeConstant*S₀ k at hk
    exact lt_of_mul_lt_mul_left (a:=G.slopeConstant) (by linarith) slope.le
  obtain ⟨j,eq,below,above⟩:=first C (S₀ k-v) (sub_pos.mpr hs)
  have le : crossing C (S₀ k-v)≤k := Nat.find_min' (passes C _) (by linarith : S₀ k-v≤S₀ k)
  have hjk : j≤k := by omega
  have hj:=RG16.Literal.lambda_up C j
  have hh:=log_le_log (log_pos (by linarith : 1<Λ₀ j))
    (log_le_log (RG16.Literal.lambda_pos C j) ((RG16.Literal.lambda_mono C hG).monotone hjk))
  refine ⟨le,?_,?_⟩
  · change v-log (log (Λ₀ k))≤S₀ k-S₀ (crossing C (S₀ k-v))
    rw [eq];linarith [jump C slow j]
  · change S₀ k-S₀ (crossing C (S₀ k-v))≤v
    rw [eq];linarith

end YM.Integration.WilsonPhysicalExteriorMeshStops
end
