import YM.WilsonCoeffUV.Emit.ProfileCharge

/-! The outer smooth test in the native coordinates of its selected home. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentFittedExteriorProfile
open Filter Function Lattice RG WilsonCoeffUV WilsonCoeffUV.Layout WilsonCoeffUV.Mer WilsonCoeffUV.Embroider
open scoped Topology BigOperators ContDiff
variable {D j:ℕ}

def shift (f:Phrase D)(c:Point4):Phrase D:=
  ⟨fun x=>f.val (-c+x),(scribble f le_rfl).comp (contDiff_const.add contDiff_id)⟩

theorem shifted (f:Phrase D)(c:Point4)(v:Fin j→Axis)(x:Point4):
    crease (shift f c) v x=crease f v (-c+x):=by
  change iteratedFDeriv ℝ j (fun z=>f.val (-c+z)) x _=_
  rw [iteratedFDeriv_comp_add_left]
  rfl

theorem zoomed (φ:Rarity D)(ρ:ℝ)(p:j≤D)(v:Fin j→Axis)(z:Point4):
    crease (zoom φ ρ) v z=ρ⁻¹^4*(ρ⁻¹^j*crease φ.ψ v (ρ⁻¹ • z)):=by
  unfold crease
  change iteratedFDeriv ℝ j (ρ⁻¹^4 • _) z _=_
  rw [show iteratedFDeriv ℝ j (ρ⁻¹^4 • _) z = _ from iteratedFDeriv_const_smul_apply (a:=ρ⁻¹^4) (x:=z)
    (scribble (sonal ρ⁻¹ 0 zeroC 0 φ.ψ) p).contDiffAt]
  change ρ⁻¹^4*crease (sonal ρ⁻¹ 0 zeroC 0 φ.ψ) v z=_
  rw [currentP _ _ _ _ _ _ p,towards0]
  rfl

private theorem support (f:Phrase D)(c:Point4):
    tsupport (shift f c).val ⊆ (fun x=> -c+x) ⁻¹' (tsupport f.val):=by
  apply closure_minimal _ (isClosed_closure.preimage (continuous_const.add continuous_id))
  intro x hx
  exact subset_closure hx

def home (φ:Rarity D)(ρ:ℝ)(pos:0<ρ)(c:Point4):Rarity D where
  ψ:=shift (zoom φ ρ) c
  radius:=max 1 (‖c‖+φ.radius*ρ)
  markG:=le_max_left ..
  support:=by
    intro z hz
    have xs:=support (zoom φ ρ) c hz
    have cap:=Layout.support_pay pos φ xs
    rw [Metric.mem_closedBall,dist_zero_right] at cap ⊢
    calc ‖z‖=‖c+(-c+z)‖:=by rw [add_neg_cancel_left]
         _≤‖c‖+‖-c+z‖:=norm_add_le _ _
         _≤‖c‖+φ.radius*ρ:=by linarith only [cap]
         _≤_:=le_max_right ..

theorem jet (φ:Rarity D)(ρ:ℝ)(p:0<ρ)(c z:Point4)(hj:j≤D)(v:Fin j→Axis):
    crease (home φ ρ p c).ψ v z=ρ⁻¹^4*(ρ⁻¹^j*crease φ.ψ v (ρ⁻¹ • (-c+z))):=by
  change crease (shift _ _) _ _=_
  rw [shifted,zoomed _ _ hj]

theorem paid (φ:Rarity D)(ρ:ℝ)(p:0<ρ)(c:Point4)(A:ℝ)(bill:Amplitude φ A):
    Amplitude (home φ ρ p c) (ρ⁻¹^4*((max 1 ρ⁻¹)^D*A)):=by
  have a:=bill.1
  have b:0≤ρ⁻¹:=(inv_pos.mpr p).le
  have m:1 ≤ max 1 ρ⁻¹:=le_max_left ..
  refine ⟨by positivity,?_⟩
  intro j hj v x
  rw [jet _ _ p _ _ hj,norm_mul,norm_mul,Real.norm_of_nonneg (pow_nonneg b _),
    Real.norm_of_nonneg (pow_nonneg b _)]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg b _)
  exact mul_le_mul ((pow_le_pow_left₀ b (le_max_right 1 _) _).trans (pow_le_pow_right₀ m hj))
    (bill.2 j hj v _) (norm_nonneg _) (pow_nonneg (zero_le_one.trans m) _)

end YM.Integration.WilsonIndependentFittedExteriorProfile
