import YM.Integration.WilsonPositionProgramTrialPublicJointSpectrum
import YM.Integration.WilsonSeparatedPrefixMovingJointIntegral

/-! Every Fourier mode of a joint position test enters one preassigned optical chamber at a common derivative wage. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicJointRoom
open RG WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer WilsonCoeffUV.Embroider Precision Lattice MeasureTheory
open WilsonSeparatedPrefixMovingJointSpectrum (Euclid character physical)
open WilsonSeparatedPrefixMovingJointExpansion (angle)
open WilsonSeparatedPrefixMovingJointWaves (sheet)
open WilsonPositionProgramTrialPublicJointSpectrum (mode spectrum)
open scoped Classical BigOperators Topology ContDiff SchwartzMap
variable {n:ℕ}

def tint {D:ℕ}(T:Rarity D)(s:ℝ):Rarity D where
  ψ:=⟨s • T.ψ.val,(scribble T.ψ le_rfl).const_smul s⟩
  radius:=T.radius
  markG:=T.markG
  support:=by
    apply Set.Subset.trans _ T.support
    exact closure_mono (fun z h=>right_ne_zero_of_mul (show s*T.ψ.val z≠0 from h))

theorem marks {D:ℕ}(T:Rarity D)(s:ℝ){j:ℕ}(hj:j≤D)(v:Fin j→Axis)(x:Point4):
    crease (tint T s).ψ v x=s*crease T.ψ v x:=by
  change iteratedFDeriv ℝ j (s • T.ψ.val) x _=_
  rw [iteratedFDeriv_const_smul_apply ((scribble T.ψ hj).contDiffAt)]
  rfl

def base:ℝ:=1+2*Real.pi*‖physical.symm.toContinuousLinearMap‖
def width (ξ:Points n):ℝ:=base*max 1 ‖ξ‖
theorem big (ξ:Points n):1≤width ξ:=by
  have h:1≤base:=by unfold base; exact le_add_of_nonneg_right (by positivity)
  exact one_le_mul_of_one_le_of_one_le h (le_max_left ..)

theorem major (ξ:Points n)(i:Fin n):1+‖angle (ξ i)‖≤width ξ:=by
  let C:=2*Real.pi*‖physical.symm.toContinuousLinearMap‖
  have h:0≤C:=by dsimp [C];positivity
  have j:=WilsonSeparatedPrefixMovingJointExpansion.price (ξ i)
  have part:‖ξ i‖≤ max 1 ‖ξ‖:=(PiLp.norm_apply_le ξ i).trans (le_max_right ..)
  change 1+‖angle (ξ i)‖≤(1+C)*max 1 ‖ξ‖
  rw [add_mul,one_mul]
  exact add_le_add (le_max_left ..) (j.trans (mul_le_mul_of_nonneg_left part h))

def normalized {D:Fin n→ℕ}(T:(i:Fin n)→Rarity (D i))(ξ:Points n)(c:Fin n→Bool)(i:Fin n):Rarity (D i):=
  tint (mode T ξ c i) ((width ξ)^(D i))⁻¹

theorem support {D:Fin n→ℕ}(T:(i:Fin n)→Rarity (D i))(ξ:Points n)(c:Fin n→Bool)(i:Fin n):
    tsupport (normalized T ξ c i).ψ.val⊆tsupport (T i).ψ.val:=by
  apply closure_mono
  intro z hit
  change (width ξ ^ D i)⁻¹*((T i).ψ.val z*_)≠0 at hit
  exact left_ne_zero_of_mul (right_ne_zero_of_mul hit)

theorem amplitude {D:Fin n→ℕ}(T:(i:Fin n)→Rarity (D i))(smooth:∀i,ContDiff ℝ ∞ (T i).ψ.val):
    ∃A:Fin n→ℝ,∀ξ c i,Amplitude (normalized T ξ c i) (A i):=by
  choose A ap lanes using fun i=>WilsonSeparatedPrefixMovingJointWaves.original (T i) (smooth i)
  refine ⟨A,?_⟩
  intro ξ c i
  refine ⟨ap i,?_⟩
  intro j hj v z
  rw [normalized,marks _ _ hj,norm_mul,Real.norm_of_nonneg (inv_nonneg.mpr (pow_nonneg ((by norm_num:0≤(1:ℝ)).trans (big ξ)) _))]
  have cap:= (lanes i (angle (ξ i)) (c i)).2 j hj v z
  have cmp: (1+‖angle (ξ i)‖)^(D i)≤(width ξ)^(D i):=pow_le_pow_left₀ (by positivity) (major ξ i) _
  have p:0<(width ξ)^D i:=pow_pos (lt_of_lt_of_le zero_lt_one (big ξ)) _
  calc
    _≤((width ξ)^D i)⁻¹*(A i*(width ξ)^D i):=
      mul_le_mul_of_nonneg_left (cap.trans (mul_le_mul_of_nonneg_left cmp (ap i))) (inv_nonneg.mpr p.le)
    _=A i:=by field_simp

theorem original {G:Gauge}(Q:Fin (n+1)→SealR G)(T:Wilt Q)(smooth:∀i,ContDiff ℝ ∞ (T i).ψ.val)
    (y Z:ℝ)(M:Fin (n+1)→ℝ)(room:Bough Q T y Z M):
    ∃A:Fin (n+1)→ℝ,∀ξ c,Bough Q (normalized T ξ c) y Z A:=by
  obtain ⟨A,fee⟩:=amplitude T smooth
  refine ⟨A,fun ξ c=>⟨room.pos,fee ξ c,room.rents,room.room,?_⟩⟩
  intro i j ne x hx z hz
  exact room.seats i j ne x (support T ξ c i hx) z (support T ξ c j hz)

end YM.Integration.WilsonPositionProgramTrialPublicJointRoom
end
