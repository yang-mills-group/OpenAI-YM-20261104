import YM.Integration.WilsonMacroscopicRichDistantPoint
import YM.RG17.Cord

/-! Relative positions of the originally prescribed two-point test. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichTestGeometry
open Function Filter Set MeasureTheory YM.RG17 YM.OPE YM.Spec YM.Extraction YM.Table
open WilsonMacroscopicRichMovingPlane
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}{n:ℕ}

def relative (z:Points 2):Points 1:=points fun i=>z i.succ-z 0
private lemma coordinate {m:ℕ}(i:Fin m):Continuous fun z:Points m=>z i:=
  (continuous_apply i).comp (PiLp.continuousLinearEquiv 2 ℝ (fun _:Fin m=>E4)).continuous
theorem continuous_relative:Continuous relative:=(PiLp.continuous_toLp 2 _).comp
  (continuous_pi fun i=>(coordinate i.succ).sub (coordinate 0))

theorem support (φ:Test 2):IsCompact (relative '' tsupport φ) ∧ ∀y∈relative '' tsupport φ,y 0≠0:=by
  refine ⟨φ.hasCompactSupport.image continuous_relative,?_⟩
  rintro _ ⟨z,hz,rfl⟩ h
  exact (φ.tsupport_subset hz).ne (Fin.succ_ne_zero (0:Fin 1)) (sub_eq_zero.mp h)

theorem clearance (K:Set (Points n))(hK:IsCompact K)(xSafe:K⊆conf n)(φ:Test 2):
    ∃η:ℝ,0<η ∧ ∀r τ:ℝ,0<r → 0<τ → r/τ≤η → ∀x∈K,∀z∈tsupport φ,
      placed r τ x (relative z) ∈ conf (n+1):=by
  obtain ⟨M,_,mpos,_,room⟩:=RG17.roomCosts hK xSafe
  obtain ⟨_,δ,_,dpos,far⟩:=RG17.roomCosts φ.hasCompactSupport φ.tsupport_subset
  refine ⟨δ/(M+1),div_pos dpos (by linarith),?_⟩
  intro r τ rp tp ratio x hx z hz
  have cross (i:Fin n)(j:Fin 1):r•x i ≠ τ•(relative z) j:=by
    have near:‖x i‖≤M:=by simpa [posed] using (room 1 one_pos x hx).span i
    have away:δ≤‖relative z j‖:=by simpa [posed,relative] using (far 1 one_pos z hz).spaced j.succ 0 (Fin.succ_ne_zero j)
    have width:r*(M+1)≤τ*δ:=by
      have t: r≤δ/(M+1)*τ:=(div_le_iff₀ tp).mp ratio
      calc r*(M+1)≤(δ/(M+1)*τ)*(M+1):=mul_le_mul_of_nonneg_right t (by linarith)
           _=τ*δ:=by field_simp [show M+1≠0 by linarith]
    intro e
    have ne:=congrArg norm e
    simp only [norm_smul_of_nonneg rp.le,norm_smul_of_nonneg tp.le] at ne
    linarith only [mul_le_mul_of_nonneg_left near rp.le,mul_le_mul_of_nonneg_left away tp.le,rp,width,ne]
  intro i j
  change Fin.append (fun i=>r•x i) (fun j=>τ•relative z j) i=Fin.append (fun i=>r•x i) (fun j=>τ•relative z j) j → i=j
  cases i using Fin.addCases <;> cases j using Fin.addCases <;> simp only [Fin.append_left,Fin.append_right]
  · intro e;exact congrArg _ (xSafe hx ((smul_right_injective _ rp.ne') e))
  · intro e;exact (cross _ _ e).elim
  · intro e;exact (cross _ _ e.symm).elim
  · intro _;exact congrArg _ (Subsingleton.elim _ _)

theorem rebased {r τ:ℝ}(x:Points n)(z:Points 2):
    absCord n 1 r (x,openRoot ((0:E4),τ•relative z))=placed r τ x (relative z):=by
  simp [absCord,pad_xy,placed];rfl
end YM.Integration.WilsonMacroscopicRichTestGeometry
