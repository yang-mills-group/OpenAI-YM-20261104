import YM.Integration.WilsonSurveyedColorPilot

/-! Equivariance of the literal continued curvature, covariant derivative,
Yang–Mills action, antifield terms and every coefficient of its MS opening. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSurveyedColorCurvature
open Function MS MS.Plane MS.Arts MS.Arts.Pilot MS.Koszul MS.Landau MS.Native
open MS.Motif MS.Motif.Literal MS.Halo MS.Garment MS.Color
open WilsonSurveyedColorTensor WilsonSurveyedColorQuotient WilsonSurveyedColorPilot
open scoped Classical BigOperators
variable {G : Gauge} (U : G.Color ≃ₗᵢ[ℝ] G.Color)
local notation "I" => G.ColorIndex
abbrev Preserves : Prop := ∀ x y z, SchemeConversionRG11.Corona.arch (U x) (U y) (U z) =
  SchemeConversionRG11.Corona.arch x y z
variable {m : ℕ}

private theorem reorder (F : I → I → I → I → Rack G m) :
    ∑ i, ∑ j, ∑ k, ∑ p, F i j k p = ∑ k, ∑ p, ∑ i, ∑ j, F i j k p := by
  let H (a b : I×I) := F a.1 a.2 b.1 b.2
  have h : ∑ i, ∑ j, H i j = ∑ j, ∑ i, H i j := Finset.sum_comm
  simpa only [Fintype.sum_prod_type] using h

theorem jawKeep (same : Preserves U) {X Y : Mield G m} (hx : Covariant U X)
    (hy : Covariant U Y) : Covariant U (jaw G m X Y) := by
  intro i
  simp only [chew,map_sum,map_smul,productKeep,hx,hy,LinearMap.sum_apply,
    LinearMap.smul_apply,Finset.smul_sum]
  rw [reorder]
  conv_rhs => rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp_rw [smul_smul,← Finset.sum_smul]
  congr 1
  have h (j k : I) : rune j k i * (entry U k b * entry U j a) =
      (realEntry U j a * realEntry U k b * letterLie j k i : ℝ) := by
    push_cast [entry,realEntry,rune]; ring
  have d (j : I) : entry U i j * rune a b j =
      (letterLie a b j * realEntry U i j : ℝ) := by
    push_cast [entry,realEntry,rune]; ring
  simp_rw [h,d,← Complex.ofReal_sum,structureConstants U same]

theorem covariantDerivative (same : Preserves U) (z : ℂ) (a : Arts.L m)
    {X : Mield G m} (hx : Covariant U X) : Covariant U (convoke z a X) := by
  rw [convoke,LinearMap.add_apply,LinearMap.smul_apply]
  exact Covariant.add U (Covariant.grad U hx a)
    (Covariant.scale U (jawKeep U same (leaf U false (some a)) hx) z)

theorem curvature (same : Preserves U) (z : ℂ) (a b : Arts.L m) :
    Covariant U (cur z a b : Mield G m) :=
  Covariant.add U (Covariant.sub U (Covariant.grad U (leaf U false (some b)) a)
    (Covariant.grad U (leaf U false (some a)) b))
    (Covariant.scale U (jawKeep U same (leaf U false (some a)) (leaf U false (some b))) z)

theorem metric {E F W : Type} [AddCommMonoid E] [Module ℂ E]
    [AddCommMonoid F] [Module ℂ F] [AddCommMonoid W] [Module ℂ W]
    (L : E →ₗ[ℂ] F →ₗ[ℂ] W) (f : I → E) (g : I → F) :
    (∑ i, L (∑ a, entry U i a • f a) (∑ b, entry U i b • g b)) =
      ∑ j, L (f j) (g j) := by
  simp only [map_sum,map_smul,LinearMap.smul_apply,LinearMap.sum_apply,Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul,sewn]
  simp [ite_smul]

theorem innerKeep {X Y : Mield G m} (hx : Covariant U X) (hy : Covariant U Y) :
    turn U (sume X Y) = sume X Y := by
  unfold sume
  simp_rw [map_sum,productKeep,hx,hy]
  exact metric U _ _ _

theorem action (same : Preserves U) (z : ℂ) (m : ℕ) :
    turn U (ploy G z m) = ploy G z m := by
  have field (a : Arts.L m) :
      turn U (sume (lip true (some a)) (convoke z a (cwave m G))) =
        sume (lip true (some a)) (convoke z a (cwave m G)) :=
    innerKeep U (leaf U true (some a)) (covariantDerivative U same z a (leaf U false none))
  have ghost : turn U (sume (lip true none) (Sc z G m)) = sume (lip true none) (Sc z G m) :=
    innerKeep U (leaf U true none) (Covariant.scale U
      (jawKeep U same (leaf U false none) (leaf U false none)) _)
  simp only [ploy,Motif.core,Surf.reach,map_sum,map_smul,map_add,map_sub]
  simp_rw [innerKeep U (curvature U same z _ _) (curvature U same z _ _), field, ghost]

theorem opening (same : Preserves U) (h m : ℕ) :
    turn U (pulseX G h m) = pulseX G h m := by
  let K := χ G
  have zread (z : ℂ) : turn U (value (Mob G) z K m) = value (Mob G) z K m := by
    rw [Class_at,Pi.sub_apply,map_sub,action U same,action U same]
  funext w
  let A := Garment.Wave.slice w
  let B := (LinearMap.proj w : Rack G m →ₗ[ℂ] ℂ).comp
    ((turn U).comp (LinearMap.proj m : Mob G →ₗ[ℂ] Rack G m))
  exact sub_eq_zero.mp (valuedZ K (B-A) (fun z => sub_eq_zero.mpr (congrFun (zread z) w)) h)

end YM.Integration.WilsonSurveyedColorCurvature
end
