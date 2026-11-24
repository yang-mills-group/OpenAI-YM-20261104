import YM.Integration.OPEMSReport
import YM.Integration.SignedTreeDilation

/-! The original MS shell basis and its grade-preserving change of coordinates to the selected RG11 field rows. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.OPEProjectedMSRows
open Set Function MS MS.Menus MS.Theater MS.Land MS.Book
open FVA2 FVA2.ColorCode Pert.Position Pert.RawLabels Pert.Scale Extra.FD
open RG11.Fields RG11.Grove RG11.Neighborhood
open scoped BigOperators Classical

variable {G : Gauge} (F : Labels.Frames G) {d i n m : ℕ}

theorem shell_basis (a : BasisIx G d) :
    exactField F d (sameAxis F d a) = Daylight (wings G) d a := by
  simp only [sameAxis,Module.Basis.map_apply,LinearEquiv.apply_symm_apply]

theorem named_dilation (a : BasisIx G d) (t : ℝ) :
    gear F d t (sameAxis F d a) = (t : ℂ)^a.size • sameAxis F d a := by
  rw [← physical_round F (sameAxis F d a),gear_inherit,
    grow_weights (w:=a.size) (p:=physicalLabel F d (sameAxis F d a)) (fun b hb => ?_) t,map_smul]
  exact congrArg Prod.fst ((Labels.weight_slot b).symm.trans
    (((Labels.pure_grade _ _).mp (FVA2.ColorCode.graded F a)) hb))

theorem eigen_coordinate {I U : Type*} [Fintype I] [AddCommGroup U] [Module ℂ U]
    (b : Module.Basis I ℂ U) (T : U →ₗ[ℂ] U) (w : I → ℕ)
    (h : ∀ j, T (b j) = (2:ℂ)^(w j) • b j) (v : U) (k : ℕ)
    (hv : T v = (2:ℂ)^k • v) (j : I) (hj : b.coord j v ≠ 0) : w j = k := by
  have he : (b.coord j).comp T = (2:ℂ)^(w j) • b.coord j := by
    apply b.ext
    intro q
    rw [LinearMap.comp_apply,h,map_smul,LinearMap.smul_apply]
    by_cases hq : j=q
    · subst q
      rfl
    · simp [Module.Basis.coord_apply,Module.Basis.repr_self,hq]
  have hp := DFunLike.congr_fun he v
  change b.coord j (T v) = (2:ℂ)^(w j) • b.coord j v at hp
  rw [hv,map_smul] at hp
  have hC : (2:ℂ)^k = 2^(w j) := mul_right_cancel₀ hj hp
  have hR : (2:ℝ)^k = 2^(w j) := by exact_mod_cast hC
  exact ((pow_right_strictMono₀ (by norm_num : (1:ℝ) < 2)).injective hR).symm

theorem input_grade (a : lab F d) (j : BasisIx G d)
    (h : (sameAxis F d).coord j ((tower F d).b a) ≠ 0) : j.size = RG11.Window.grade F d a :=
  eigen_coordinate (sameAxis F d) (gear F d 2) (fun q => q.size) (fun q => named_dilation F q 2)
    ((tower F d).b a) _ (SignedTreeDilation.gear_basis F a 2) j h

theorem output_grade (a : lab F d) (j : BasisIx G d)
    (h : (tower F d).b.coord a (sameAxis F d j) ≠ 0) : RG11.Window.grade F d a = j.size :=
  eigen_coordinate (tower F d).b (gear F d 2) (RG11.Window.grade F d)
    (fun q => SignedTreeDilation.gear_basis F q 2) (sameAxis F d j) j.size (named_dilation F j 2) a h

def weights (v : Fin n → E F d) (j : Fin n → BasisIx G d) : ℂ :=
  ∏ a, (sameAxis F d).coord (j a) (v a)

theorem total_grade (u : sheaf F n d) (j : Fin n → BasisIx G d)
    (h : weights F ((tower F d).b ∘ u) j ≠ 0) : ∑ a, (j a).size = worth u := by
  apply Finset.sum_congr rfl
  intro a _
  apply input_grade F (u a) (j a)
  exact (Finset.prod_ne_zero_iff.mp h) a (Finset.mem_univ a)

variable (V : Warehouse G) {Q : Booked (wings G)} (M : MS_Data G Q) (μ : ℝ)

def named_row (k : ℕ) (x : Points n) (v : Fin n → E V.F d) : ℂ :=
  ∑ j : Fin n → BasisIx G d, weights V.F v j *
    MS.Dial.tour M (labelAt (wings G) ∘ j) μ (fun a => Theater.out (x a)) Finset.univ k

theorem row (k : ℕ) (x : Points n) (v : Fin n → E V.F d) :
    Fountain.phys V M μ k x d v = named_row V M μ k x v :=
  PositionX.Bare.spread_value (sameAxis V.F d) (fun p => Fountain.score M μ k p x) v

theorem front (x : conf n) (y : Tail m) (s : ℝ) (hx : driven (Real.exp (-s)) x.val y ∈ conf (n+m))
    (u : sheaf V.F n i) (v : sheaf V.F m d) (k : ℕ) :
    PowerSeries.coeff k (frontRow (OPEMSReport.report V M μ) i d (.inl x) y s u v) =
      named_row V M μ k (driven (Real.exp (-s)) x.val y) (OPEMSReport.jointLabels V u v) :=
  (OPEMSReport.front_point V M μ x y s hx u v k).trans (row V M μ _ _ _)

theorem profile (f : Test n) (y : Tail m) (s : ℝ)
    (hf : ∀ x ∈ tsupport f, driven (Real.exp (-s)) x y ∈ conf (n+m))
    (u : sheaf V.F n i) (v : sheaf V.F m d) (k : ℕ) :
    PowerSeries.coeff k (frontRow (OPEMSReport.report V M μ) i d (.inr f) y s u v) =
      f.applyTo (fun x => named_row V M μ k (driven (Real.exp (-s)) x y)
        (OPEMSReport.jointLabels V u v)) := by
  rw [OPEMSReport.front_test V M μ f y s hf u v k]
  exact congrArg f.applyTo (funext fun x => row V M μ _ _ _)

theorem back (y : Tail m) (a : lab V.F i) (v : sheaf V.F m d) (k : ℕ) :
    PowerSeries.coeff k (backRow (OPEMSReport.report V M μ) i d y a v) =
      named_row V M μ k (close y) (OPEMSReport.jointLabels V (fun _ : Fin 1 => a) v) :=
  (OPEMSReport.back_point V M μ y a v k).trans (row V M μ _ _ _)

end YM.Integration.OPEProjectedMSRows
