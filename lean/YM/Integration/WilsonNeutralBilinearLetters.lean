import YM.Integration.WilsonNeutralBilinearCoordinates
import YM.Integration.WilsonNeutralNativeFreeStep
/-! At horizon four the nonunit letter of the full tested formal programme
is precisely a nonunit physical coefficient. There is no independent
test-derivative axis in this sector. All such columns share the same
engineering normalization and the full free matrix is the identity. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonNeutralBilinearLetters
open FormalBulk08 Matrix Laurent Precision Exterior PowerSeries Lattice RG Wilson Tree Stationary
open Push.Uniform Bloch Reef Jets Orb Wick Flat Next.Free UVExtension.Free
open Function Filter Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Dawn Wine Rial Roof Dove
open Planned.PrimaryIntegral295 Source Source.Drops Labels PhysicalNext.Repeat.Legato Next.Foundations
open WilsonRunFormalMarkedStep WilsonNeutralNormalizedForestStep
open scoped Topology BigOperators Matrix Classical

variable {G:Gauge}(F:Frame G 4)
def plain (k:F.Index):Letter F:=
  ⟨(k,⟨0,(Dawn.paper_is 0).mpr (by simp [Chapel.upper])⟩),
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa [Chapel.upper] using F.bound k⟩⟩

theorem literal (simple:G.Simple)(v:Letter F)(awake:Pose.mint F v≠0):
    v=plain F (Pose.mint F v) ∧ Pose.weight F v=4 ∧ Pose.slots F v=2:=by
  have rank:=WilsonNeutralBilinearCoordinates.classification simple F _ awake
  have rent:=Pose.weightFits F v
  rw [Pose.weight,Pose.label,rank] at rent
  change 4+Chapel.upper (Pose.pet F v).val ≤ 4 at rent
  have empty:Chapel.upper (Pose.pet F v).val=0:=by omega
  have zero:(Pose.pet F v).val=0:=by
    funext s
    change (Pose.pet F v).val s=0
    have h:(Pose.pet F v).val s ≤ Chapel.upper (Pose.pet F v).val:=
      Finset.single_le_sum (f:=(Pose.pet F v).val) (fun u _=>Nat.zero_le _) (Finset.mem_univ s)
    omega
  refine ⟨?_,?_,?_⟩
  · apply Subtype.ext; exact Prod.ext (by rfl) (Subtype.ext zero)
  · rw [Pose.weight,empty,Nat.add_zero,Pose.label,rank]
  · exact congrArg Prod.snd rank

def fields (simple:G.Simple):
    {v:Letter F // Pose.mint F v ≠ 0} ≃ {k:F.Index // k ≠ 0} where
  toFun v:=⟨Pose.mint F v.val,v.property⟩
  invFun k:=⟨plain F k.val,k.property⟩
  left_inv v:=Subtype.ext (literal F simple v.val v.property).1.symm
  right_inv _:=rfl

variable (R:Run G){D:ℕ}(wood:Primer.Families R.family)(a:hue G)(depth:4<D){U:ℕ→ℕ}
  (grant:WilsonWindowFormalPurchase.Canonical U R.kit)
local notation "F₄" => R.family.labels.level 4
local notation "Nonunit" => {k:(F₄).Index // k ≠ 0}
def entry (N i e:ℕ)(s t:Nonunit):ℝ:=
  coeff e (Primer.fieldStep R.family a wood depth N i (plain (F₄) s.val) (plain (F₄) t.val))
include grant in
theorem free (N i:ℕ)(simple:G.Simple)(o:Loc G 1)(hi:i<N)
    (front:4 ≤ R.family.path.levels.clock.J (i+1))(s t:Nonunit):
    entry R wood a depth N i 0 s t=if s=t then 1 else 0:=by
  have sc:Pose.mint (F₄) (plain (F₄) s.val)≠0:=s.property
  have tc:Pose.mint (F₄) (plain (F₄) t.val)≠0:=t.property
  obtain ⟨_,sw,ss⟩:=literal (F₄) simple _ sc
  obtain ⟨_,tw,ts⟩:=literal (F₄) simple _ tc
  have f:=WilsonNeutralNativeFreeStep.own_weight R wood a depth grant N i simple o hi front _ _
    (ss.trans ts.symm) sw tw
  unfold entry;rw [f]
  by_cases e:s=t
  · simp [e]
  · have diff:plain (F₄) s.val≠plain (F₄) t.val:=fun same=>e (Subtype.ext (congrArg (Pose.mint (F₄)) same))
    simp [e,diff]

end YM.Integration.WilsonNeutralBilinearLetters
end
