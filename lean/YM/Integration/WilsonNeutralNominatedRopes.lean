import YM.Integration.WilsonNeutralCutoffAlphabet

/-! Apply the finite upper inverse to the two nominated cutoff columns at
their original numerical coefficients.  The source is submitted once, with
its original field normalization and both physical real functionals. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonNeutralNominatedRopes
open PowerSeries FormalBulk08 Matrix Lattice Laurent RG Wilson
open Pose Dawn Roof Grail Trellis Filter Dove
open Planned.PrimaryIntegral295 Source Labels Next.Foundations
open WilsonRunFormalMarkedStep
open Precision Exterior Tree Stationary Push.Uniform Bloch Reef Jets Orb Wick Flat Next.Free UVExtension.Free
open Function Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Glide Bank Wine Rial
open PhysicalNext.Repeat.Legato FVA1Physical.TwoReset
open WilsonNeutralCopiedProgram WilsonNeutralCopiedField WilsonNeutralCutoffAlphabet
open scoped BigOperators Classical

variable {G:Gauge} (R:Run G) {D:ℕ}(wood:Primer.Families R.family)(a:hue G)
    (depth:4<D) {U:ℕ→ℕ}(grant:WilsonWindowFormalPurchase.Canonical U R.kit)
local notation "F₄" => R.family.labels.level 4
local notation "S₀" => Primer.fieldStep R.family a wood depth
local notation "K₀" => WilsonNeutralFiledFieldReversion.kinetic R wood a
local notation "G₀" => WilsonPositionThermometerCapStation.Group R.family 6

def planted (A:G₀)(N per:ℕ)(leg:Fin 2)(phase:ℂ→ₗ[ℝ]ℝ):Pose.Letter (F₄)→Pence:=
  let x:R.family.label 4:=WilsonNeutralOffsetCutoff.named R A N per leg.succ
  let g:=ConnectedActivityE6.Coat.gStep (R.family.beta N per)
  fun v=>submitted R N per x phase g (filed (F₄) v)

include grant in
theorem original (A:G₀)(N per m h k:ℕ)(leg:Fin 2)(phase:ℂ→ₗ[ℝ]ℝ)
    (simple:G.Simple)(o:Loc G 1)(dates:m+h≤N)(front:4≤R.family.path.levels.clock.J (m+1))
    (j:{s:(F₄).Index//s≠0}):
    let slot:=WilsonNeutralBilinearLetters.plain (F₄) j
    let x:R.family.label 4:=WilsonNeutralOffsetCutoff.named R A N per leg.succ
    let g:=ConnectedActivityE6.Coat.gStep (R.family.beta N per)
    let y:=ropes (K₀ N) (S₀ N) k m h *ᵥ planted R A N per leg phase
    coeff 0 (y slot)=fee R N per x phase g j ∧ coeff 1 (y slot)=0:=by
  intro slot x g y
  let source:=planted R A N per leg phase
  let V:=ropes (K₀ N) (S₀ N) k m h
  have exact_slot:source slot=C (fee R N per x phase g j):=by
    change submitted R N per x phase g (filed (F₄) slot)=_
    rw [show filed (F₄) slot=WilsonNeutralCopiedField.point (F₄) j from point_eq (F₄) j]
    unfold submitted
    rw [show WilsonCoeffUV.Cosmos.sheet (F₄) (WilsonNeutralCopiedField.point (F₄) j)=j.val from rfl,
      if_pos rfl]
  obtain ⟨ground,first⟩:=WilsonNeutralBilinearRopes.original R wood a depth grant N m h k simple o dates front j
  change ∀v,coeff 0 (V slot v)=if slot=v then 1 else 0 at ground
  change ∀v,coeff 1 (V slot v)=0 at first
  have zero (b c:Pence):coeff 0 (b*c)=coeff 0 b*coeff 0 c:=by
    simp only [coeff_zero_eq_constantCoeff_apply,map_mul]
  have one (b c:Pence):coeff 1 (b*c)=coeff 0 b*coeff 1 c+coeff 1 b*coeff 0 c:=by
    rw [coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp [Finset.sum_range_succ]
  change coeff 0 (∑v,V slot v*source v)=_ ∧ coeff 1 (∑v,V slot v*source v)=_
  constructor
  · simp only [map_sum,zero,ground,ite_mul,one_mul,zero_mul]
    simp [exact_slot]
  · simp only [map_sum,one,ground,first,zero_mul,add_zero,ite_mul,one_mul]
    simp [exact_slot]
end YM.Integration.WilsonNeutralNominatedRopes
end
