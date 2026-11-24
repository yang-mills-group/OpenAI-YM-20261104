import YM.Integration.WilsonPhysicalStationGradedLowerPanel

/-! Uniform positive neighborhood before the coarse physical chart is elected. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickInverse
open Function Filter Finset Set Lattice Wilson RG Source Cells GapsContact.Seams Trace.Terrace
open PhysicalNext.Repeat.Legato Extraction RG17 Spec Table Table.Pairing Climb Trace.Pilot PhysMS
open Maxwell Maxwell.Wick XSpace XSpace.Normalize XSpace.Structure1
open MS MS.Land MS.Menus MS.Theater Local.Physical
open WilsonOriginalPublicRelativeGramFreePanel (named pointsAt)
open WilsonPhysicalStationLowerReceiver (ear)
open WilsonPositionProgramPublicWickGram (reading nodes)
open scoped Classical Topology BigOperators Matrix Matrix.Norms.Operator
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    (U:tower S)(B:Deck G)(e:ℕ)(a:Axis)
local notation "I" => Glyph B e
open WilsonPhysicalStationGradedLowerPanel (factor metered frame cross charge right solves)

theorem original :
    ∃δ K:ℝ,0<δ ∧ 0<K ∧ ∀(U:tower S)(x:Points 2)(T:ℝ),0<T→
      ‖(fun i j:I=>metered B e T (frame R U B e a x) i j)-reading a (nodes a) (id:I→I)‖≤δ→
      ∀(Q:ℕ)(L:S.Field e→ₗ[ℂ]ℂ),
        (∑j:I,charge R U B e a x T Q L j • ear R (e:=e) x (right R U B e j)=L) ∧
        ∀j:I,‖charge R U B e a x T Q L j‖*T^Q ≤ T^j.2.1.val*K*‖cross R U B e a T Q L‖:=by
  obtain ⟨k,δ,kp,dp,grant⟩:=WilsonOriginalPublicRelativeGramReference.original a (id:I→I) Function.injective_id
  let cap:ℝ:=∑_i:I,∑_j:I,(Fintype.card I:ℝ)/k
  have positive:0≤cap:=by dsimp [cap]; positivity
  refine ⟨δ,cap+1,dp,by linarith,?_⟩
  intro U x T tp near Q L
  let H:=metered B e T (frame R U B e a x)
  let b:=cross R U B e a T Q L
  obtain ⟨unit,small⟩:=grant H near
  refine ⟨solves R U B e a x T tp Q L unit,?_⟩
  intro j
  have bounded:= (norm_le_pi_norm (H⁻¹*ᵥ b) j).trans ((Matrix.linfty_opNorm_mulVec _ _).trans
    (mul_le_mul_of_nonneg_right small (norm_nonneg b)))
  have one:‖factor B e T j‖=T^j.2.1.val:=by simp [factor,Complex.norm_real,Real.norm_eq_abs,abs_of_pos tp]
  have sig:‖(T:ℂ)^Q‖=T^Q:=by simp [Complex.norm_real,Real.norm_eq_abs,abs_of_pos tp]
  rw [WilsonPhysicalStationGradedLowerPanel.charge,norm_mul,norm_div,one,sig]
  calc
    _ = T^j.2.1.val*‖(H⁻¹*ᵥ b) j‖ := by field_simp; rfl
    _ ≤ T^j.2.1.val*(cap*‖b‖):=mul_le_mul_of_nonneg_left bounded (pow_nonneg tp.le _)
    _ ≤ T^j.2.1.val*(cap+1)*‖b‖:=by rw [mul_assoc]; gcongr; linarith

end YM.Integration.WilsonPhysicalStationMixedWickInverse
end
