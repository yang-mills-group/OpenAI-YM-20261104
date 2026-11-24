import YM.Integration.WilsonReflectedOriginalLocatedPrefix
import YM.Integration.WilsonAddressedWeakTiling
/-! The actual origins of independently posed reflected columns at N
have the prescribed two parents at K. Their spacing is the full mesh
ratio for any two distinct reporting sites, irrespective of the period. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedEmbeddedLocations
open Filter Function Lattice Wilson RG Source Extra.Histories Cells MergeProof Accent Motion
open PhysicalNext.Repeat.Legato WilsonThermometerReflectedTrajectory
open WilsonOriginalNullOriginGridRoster WilsonReflectedOriginalLocatedPrefix
open private composed same from YM.Integration.WilsonAddressedWeakTiling
open scoped Classical
variable {G:Gauge}(R:Run G)
local notation "S₀" => R.family.S
local notation "D₀" i:max p:max => R.family.side i p

theorem count {f K:ℕ}(before:f≤K)(p:ℕ):
    (((S₀).toDepth before p).count.val:ℝ)=(S₀).a f/(S₀).a K:=by
  obtain ⟨t,rfl⟩:=Nat.exists_eq_add_of_le before
  change (((S₀).steps f (f+t-f)).val:ℝ) = _
  rw [Nat.add_sub_cancel_left,Schedule.a,Schedule.a,Schedule.den_add,PNat.mul_coe,Nat.cast_mul]
  have dp:0<(((S₀).denominator f).val:ℝ):=by exact_mod_cast ((S₀).denominator f).property
  field_simp [dp.ne']

theorem parent {f K N p:ℕ}(front:f≤K)(cut:K≤N)(x:Site (D₀ f p)):
    ancestry R p N (((S₀).toDepth (front.trans cut) p).embed x) K=
      ((S₀).toDepth front p).embed x:=by
  rw [ancestry,dif_pos cut,←composed ((S₀).toDepth front p) ((S₀).toDepth cut p) ((S₀).toDepth (front.trans cut) p)]
  exact ((S₀).toDepth cut p).embed_parent _

theorem spaced {f K N p:ℕ}(front:f≤K)(cut:K≤N)(x y:Site (D₀ f p))(different:x≠y):
    ((S₀).toDepth front p).count.val≤
      measured R N p (((S₀).toDepth (front.trans cut) p).embed x)
        (((S₀).toDepth (front.trans cut) p).embed y) K:=by
  rw [measured,parent R front cut x,parent R front cut y]
  have h:=WilsonAddressedWeakTiling.spacing R front x y different
  simpa only [anchorAt,Mix.camp,dif_pos (le_refl K),same] using h

end YM.Integration.WilsonReflectedEmbeddedLocations
end
