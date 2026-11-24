import YM.Integration.WilsonGraphCenteredFarBilinearPrice

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.FVA2.GradedFar.AppointedBilinearBook

open Function Filter Real PowerSeries Finset Continuation Growth
open Register MS MS.Native MS.Land MS.Book MS.Book.Program
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Enh O.Score O.Canon Scale Dframe Reg.Point
open scoped BigOperators Classical

section Algebra
variable {G : Gauge} (N : Register.WilsonPrescription G)

theorem columnCoordinate (h p : ℕ) (A : Guard G h) (t : ℝ) (u : Sec G h) (b : Dime G h) :
    (dime G h).repr (atColumn A p t u) b = crop p t (tax A u b) := by
  change (dime G h).coord b (atColumn A p t u) = _
  rw [YM.FVA2.GradedFar.crop_eq]
  unfold atColumn tax
  rw [LinearMap.sum_apply]
  simp_rw [LinearMap.smul_apply, map_sum, _root_.map_smul, smul_eq_mul, coeff_mk]
  rfl

private theorem unit (h : ℕ) (u : Sec G h) (b : Dime G h) :
    tax (1 : Guard G h) u b = PowerSeries.C ((dime G h).repr u b) := by
  refine PowerSeries.ext fun i => ?_
  simp only [tax, coeff_mk, coeff_one, coeff_C]
  split_ifs with hi
  · subst i; rfl
  · simp

theorem basis (h : ℕ) (x : Scale.Stage 2) (a b : Sec G h) :
    Reg.Point.story (book N h 2 x) ![a,b] =
      ∑ c : Fin 2 → Dime G h, C ((dime G h).repr a (c 0)) * C ((dime G h).repr b (c 1)) *
        Reg.Point.story (book N h 2 x) (fun i => dime G h (c i)) := by
  have issued := Reg.Point.estate (1:Guard G h) (book N h 2 x) ![a,b]
  rw [Reg.Point.home_v] at issued
  rw [issued]
  apply Finset.sum_congr rfl
  intro c _
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, unit]

private theorem finite {I : Type} [Fintype I] (p : ℕ) (t : ℝ) (F : I → PowerSeries ℂ) :
    crop p t (∑ i, F i) = ∑ i, crop p t (F i) := by
  exact YM.FVA2.GradedFar.crop_sum p t Finset.univ F

private theorem fixed (p : ℕ) (t : ℝ) (a b : ℂ) (F : PowerSeries ℂ) :
    crop p t (C a * C b * F) = a * b * crop p t F := by
  rw [←map_mul, YM.FVA2.GradedFar.crop_C_mul]

/-- Evaluating the real filed columns at the far heater produces exactly the individually
cropped coordinate products. No heater is changed in this equality. -/
theorem numerical (h p : ℕ) (x : Scale.Stage 2) (A B : Guard G h) (u v : Sec G h) (t : ℝ) :
    crop p t (Reg.Point.story (book N h 2 x) ![atColumn A p t u, atColumn B p t v]) =
      AppointedBilinearPrice.separatedCrops N h p x A B u v t := by
  rw [basis N, finite]
  unfold AppointedBilinearPrice.separatedCrops
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [fixed, columnCoordinate, columnCoordinate]

theorem farBorn (h p : ℕ) (t : ℝ) : atColumn (1 : Guard G h) p t = 1 := by
  unfold atColumn
  simp [coeff_one]

end Algebra

open YangMills YangMills.Matching YM.Answer.ContinuumLimit YM.Integration
open WilsonGraphPublishedShapeEstimate WilsonGraphPreElectedShapeEstimates
universe u
variable (g : GaugeGroup) (hg : g.IsSimple)
private abbrev Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
private abbrev Q := WilsonGraphPaperPublication.perspective.{u} g hg
private abbrev S := _root_.IssuedBridge.PostedAppointedConversion.filed
  (Z g hg) (Q.{u} g hg).MS (Q.{u} g hg).matching (Teller.logNu 1)

theorem appointed (h : ℕ) (y : Spacetime) (hy : WithLp.toLp 2 ![0,y] ∈ YM.conf 2) (a b : Sec g.core h) :
    AppointedCenteredRows.series g hg h a b y =
      Reg.Point.story (book (Z g hg) h 2 ⟨WithLp.toLp 2 ![0,y],hy⟩) ![a,b] := by
  let far : YM.Points 1 := WithLp.toLp 2 (fun _ => y)
  have pos : forest (0 : YM.Points 1) (squeeze (-(0:ℝ)) far) = WithLp.toLp 2 ![0,y] := by
    simp only [squeeze,neg_zero,Real.exp_zero,one_smul]
    apply congrArg (WithLp.toLp 2)
    funext i
    fin_cases i <;> rfl
  have hp : forest (0 : YM.Points 1) (squeeze (-(0:ℝ)) far) ∈ YM.conf (1+1) := by rwa [pos]
  refine PowerSeries.ext fun j => ?_
  have port := Continuation.coeff_row (d:=fun _ : Fin 1 => h) (e:=fun _ : Fin 1 => h)
    (Q.{0} g hg).matching 0 (fun _ => a) far (fun _ => b) 0 (fun _ => le_refl h) (fun _ => le_refl h) hp j
  change coeff j (Continuation.row (Z g hg) (d:=fun _ : Fin 1 => h) (e:=fun _ : Fin 1 => h)
    0 (fun _ => a) far (fun _ => b) 0) = _
  rw [port]
  simp only [Reg.Point.story,coeff_mk]
  have roster : Fin.append (installedInputs (d:=fun _ : Fin 1 => h) (fun _ => le_refl h) (fun _ => a))
      (installedInputs (d:=fun _ : Fin 1 => h) (fun _ => le_refl h) (fun _ => b)) = ![a,b] := by
    funext i
    fin_cases i <;> rfl
  rw [roster]
  have stage : (⟨forest (0 : YM.Points 1) (squeeze (-(0:ℝ)) far), hp⟩ : Scale.Stage 2) = ⟨WithLp.toLp 2 ![0,y],hy⟩ := Subtype.ext pos
  rw [stage]

include g hg in
theorem publicValue (h p : ℕ) (y : Spacetime) (hy : WithLp.toLp 2 ![0,y] ∈ YM.conf 2)
    (A B : Guard g.core h) (u v : Sec g.core h) (t : ℝ) :
    (∑ i : Fin (p+1), (t:ℂ)^i.val * WilsonGraphStandaloneCorrelation.converted
      (S.{u} g hg) i.val (publicLetters (fun _ : Fin 2 => h) ![atColumn A p t u,atColumn B p t v])
      (WithLp.toLp 2 ![0,y])) =
    AppointedBilinearPrice.separatedCrops (Z g hg) h p ⟨WithLp.toLp 2 ![0,y],hy⟩ A B u v t := by
  rw [←AppointedCenteredRows.centeredCrop.{u} g hg h p _ _ y t hy, appointed g hg h y hy, numerical]

end YM.FVA2.GradedFar.AppointedBilinearBook
