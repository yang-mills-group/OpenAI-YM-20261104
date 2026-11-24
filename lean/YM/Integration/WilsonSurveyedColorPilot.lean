import YM.Integration.WilsonSurveyedColorQuotient
import YM.Integration.WilsonSurveyedColorVertices
import YangMills.WilsonProof.NativeSupport.YM.MS.Halo.Madd

/-! The color map as an actual field substitution on the dimensional MS
action and its covariant curvature and derivative slots. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSurveyedColorPilot
open Function MS MS.Plane MS.Arts MS.Arts.Pilot MS.Koszul MS.Landau MS.Native
open MS.Motif MS.Halo MS.Garment MS.Color WilsonSurveyedColorTensor
open WilsonSurveyedColorQuotient
open scoped Classical BigOperators
variable {G : Gauge} (U : G.Color ≃ₗᵢ[ℝ] G.Color)
local notation "I" => G.ColorIndex
def realEntry (i j : I) : ℝ := U (baseC j) i

theorem coordinates (x : G.Color) (a : I) :
    U x a = ∑ j, realEntry U a j * x j := by
  nth_rw 1 [← MS.Landau.color_sum x]
  rw [map_sum,WithLp.ofLp_sum,Finset.sum_apply]
  simp only [map_smul,PiLp.smul_apply,smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm ..

theorem structureConstants
    (same : ∀ x y z, SchemeConversionRG11.Corona.arch (U x) (U y) (U z) =
      SchemeConversionRG11.Corona.arch x y z) (a b c : I) :
    ∑ i, ∑ j, realEntry U i a * realEntry U j b * letterLie i j c =
      ∑ k, letterLie a b k * realEntry U c k := by
  have he := congrArg (fun x : G.Color => x c) (bracket U same (baseC a) (baseC b)).symm
  dsimp only at he
  have base (i : I) : ∑ k, realEntry U k i • baseC k = U (baseC i) := MS.Landau.color_sum _
  nth_rw 1 [← base a, ← base b] at he
  simp only [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply,Finset.smul_sum,
    smul_smul,WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,smul_eq_mul] at he
  rw [coordinates] at he
  rw [Finset.sum_comm]
  simp_rw [mul_comm (realEntry U _ a) (realEntry U _ b)]
  exact he.trans (Finset.sum_congr rfl fun i _ => mul_comm ..)

variable {D P : Type} [Fintype D] [DecidableEq D] [AddCommGroup P]
def pilot : Pilot ℂ P (Landau.parity (C:=I) (A:=D)) where
  volp := AddEquiv.refl _
  fieldC a b := if a.1=b.1 then entry U b.2 a.2 else 0
  pair_zero a b h := by split_ifs at h with ht; exact congrArg Landau.p ht; contradiction

theorem emits : (pilot (D:=D) (P:=P) U).beam = turn U := by
  apply LinearMap.ext
  intro F
  funext w
  induction w generalizing F with
  | nil => rw [peeps]; rfl
  | cons a w ih =>
    rw [Pilot.met, D_eval a (turn U F), derivative, Finset.sum_apply, Fintype.sum_prod_type]
    simp only [ih]
    simp [pilot,MS.Color.setLeg,ite_mul]

variable {m : ℕ}
abbrev Covariant (X : Mield G m) := ∀ i : I, turn U (X i) = ∑ j, entry U i j • X j

theorem productKeep (x y : Rack G m) :
    turn U (bite m G x y) = bite m G (turn U x) (turn U y) := by
  simpa only [emits] using Pilot.circle_prod (pilot U) x y

theorem momentum (a : Arts.L m) (F : Rack G m) :
    turn U (rowP a F) = rowP a (turn U F) := by
  funext w
  rw [← emits,rowP,beamMoon,moon]
  rfl

lemma leaf (flag : Bool) (a : Option (Arts.L m)) :
    Covariant U (lip flag a) := by
  intro j
  funext w
  rw [← emits,lip,usesLeaf]
  rcases w with _|⟨⟨⟨i,s⟩,p⟩,_|w⟩ <;>
    simp [Finset.sum_apply,lip,Motif.leaf,note,mono,pilot,onX]
  by_cases hx : i=(a,flag) <;> simp [hx]

namespace Covariant
variable {X Y : Mield G m}
theorem add (hx : Covariant U X) (hy : Covariant U Y) : Covariant U (X+Y) := by
  intro i
  simp_rw [Pi.add_apply,map_add,smul_add,hx,hy,Finset.sum_add_distrib]
theorem sub (hx : Covariant U X) (hy : Covariant U Y) : Covariant U (X-Y) := by
  intro i
  simp_rw [Pi.sub_apply,map_sub,smul_sub,hx,hy,Finset.sum_sub_distrib]
theorem scale (hx : Covariant U X) (s : ℂ) : Covariant U (s • X) := by
  intro i
  simp_rw [Pi.smul_apply,map_smul,hx,Finset.smul_sum,smul_comm s _]
theorem grad (hx : Covariant U X) (a : Arts.L m) : Covariant U (axisP a X) := by
  intro i
  simp_rw [axisP,lock,momentum,hx,map_sum,map_smul]
end Covariant

end YM.Integration.WilsonSurveyedColorPilot
end
