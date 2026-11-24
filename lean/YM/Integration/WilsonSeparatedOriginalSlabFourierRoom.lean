import YM.Integration.WilsonSeparatedOriginalSlabFourierPositions
import YM.Integration.WilsonSeparatedOriginalSlabCompactFourier

/-! A single true compact Fourier torus covers the entire original three-arm subcell profile before the period or ultraviolet cutoff. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalSlabFourierRoom
open Filter Function Set Metric Lattice Wilson RG05Readout RG05Readout.Native RG05Readout.Nuclear RG05Readout.Pulse
open WilsonSeparatedOriginalSlabFourierPositions WilsonSeparatedOriginalSlabFourierLattice
open private location from YM.Integration.WilsonSeparatedOriginalReplicaRegularity
open scoped Topology BigOperators Classical ContDiff
local notation "Y"=>Cloud (Fin 3)
local notation "X"=>Axes→ℝ

def index:Y→L[ℝ]X:=ContinuousLinearMap.pi (fun j:Axes=> ((ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:Axis=>ℝ) j.2).comp
  (PiLp.continuousLinearEquiv 2 ℝ (fun _:Axis=>ℝ)).toContinuousLinearMap).comp (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:Fin 3=>E4) j.1))

def frame (P:ℝ):X→L[ℝ]Y:=P • form

def cursor (P:ℝ):Y→L[ℝ]X:=P⁻¹ • index

theorem physical {P:ℝ}(hp:0<P)(v:Y):frame P (cursor P v)=v:=by
  ext i d
  change P*(P⁻¹*(v i d))=v i d
  field_simp

def edge {G:Gauge}(C:Family G)(b J:ℕ)(r cap:ℝ):ℝ:=4*(1+cap+gross C b J r)

private theorem nonneg {G:Gauge}(C:Family G)(b J:ℕ){r:ℝ}(rp:0<r):0≤gross C b J r:=by
  have:=C.S.a_pos b;unfold gross;positivity

theorem room {G:Gauge}(C:Family G)(b J:ℕ){r cap:ℝ}(rp:0<r)(cp:0≤cap):
    0<edge C b J r cap ∧ 4*cap≤edge C b J r cap ∧ 4*gross C b J r≤edge C b J r cap:=by
  have h:=nonneg C b J rp;unfold edge;constructor <;> [linarith;constructor <;>linarith]

theorem central {G:Gauge}{C:Family G}{b N per:ℕ}(J:ℕ)(o:Fin 3→Site (C.side b per))
    (admit:o∈Pulse.area (C:=C) (b:=b) (p:=per) J)(top:b≤N){r cap:ℝ}(rp:0<r)(cp:0≤cap)
    (t:Fin 3→Site (C.S.toDepth top per).count){z:E4}(hz:z∈Native.box):
    1/4+dist (cursor (edge C b J r cap) (location o top r t z)) 0<1:=by
  let P:=edge C b J r cap
  obtain ⟨hp,_,hc⟩:=room C b J rp cp
  rw [dist_zero_right]
  change 1/4+‖P⁻¹ • axes (location o top r t z)‖<1
  rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hp.le)]
  have h:=held J o admit top rp t hz
  have fine:P⁻¹*‖axes (location o top r t z)‖≤1/4:=by
    rw [←div_eq_inv_mul,div_le_iff₀ hp];linarith
  linarith

def lift (P:ℝ)(Ψ:Wave (Fin 3)):X→ℂ:=Ψ.val ∘ frame P

theorem shape {P cap:ℝ}(hp:0<P)(space:4*cap≤P)(Ψ:Wave (Fin 3))
    (seen:∀y∈tsupport Ψ.val,∀i,‖y i‖≤cap):support (lift P Ψ)⊆closedBall 0 (1/4):=by
  intro x hx
  rw [mem_closedBall_zero_iff]
  apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
  intro j
  have inside:=seen (frame P x) (subset_closure (show frame P x∈Function.support Ψ.val from hx)) j.1
  have coord:‖P * x j‖≤cap:=(PiLp.norm_apply_le ((frame P x) j.1) j.2).trans inside
  rw [norm_mul,Real.norm_of_nonneg hp.le] at coord
  exact (le_of_mul_le_mul_left (by linarith : P*‖x j‖≤P*(1/4)) hp)

def bank (P:ℝ)(M:ℕ)(B:ℝ):ℝ:= (max 1 ‖frame P‖)^M*B

theorem derivative (P:ℝ)(M:ℕ){B:ℝ}(bp:0≤B)(Ψ:Wave (Fin 3))(fund:Tall Ψ M 1 B)(h:ℕ)(age:h≤M)(x:X):
    ‖iteratedFDeriv ℝ h (lift P Ψ) x‖≤bank P M B:=by
  change ‖iteratedFDeriv ℝ h (Ψ.val ∘ frame P) x‖≤_
  rw [(frame P).iteratedFDeriv_comp_right (lit Ψ h) x (i:=h) le_rfl]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  have spent:‖iteratedFDeriv ℝ h Ψ.val (frame P x)‖≤B:=by simpa only [one_pow,one_mul] using fund h age (frame P x)
  have linear:‖frame P‖^h≤(max 1 ‖frame P‖)^M:=(pow_le_pow_left₀ (norm_nonneg _) (le_max_right ..) h).trans (pow_le_pow_right₀ (le_max_left ..) age)
  simpa only [bank,mul_comm B] using mul_le_mul spent linear (pow_nonneg (norm_nonneg _) _) bp

end YM.Integration.WilsonSeparatedOriginalSlabFourierRoom
