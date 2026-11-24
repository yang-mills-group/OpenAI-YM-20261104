import YM.Integration.WilsonMacroscopicSpatialDerivatives

/-! The cost of an actual differentiated running input follows from the
uniform physical mixed two-site derivative and the original reflected
Gram. No intertwining of J with the continuum derivative is assumed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMacroscopicDescendant
open Function Filter Finset Set MeasureTheory Extraction Table
open Spec Next.Rank OPE OPE.Orbits RG12 RG17 SharpGram Climb PhysMS
open OPE.Levy Push.FiniteDetection.Free Trace.Pilot
open scoped Topology Classical BigOperators ContDiff
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {V : Table C.book}

def ribbon {E : ℕ→Type*} {d e : ℕ} (v : E d) (w : E e) : (i : Fin 2)→ E (![d,e] i) :=
  Fin.cases v (Fin.cases w (fun i=>i.elim0))

local instance (T : Table C.book) (d : ℕ) : FiniteDimensional ℝ (T.Field d) := Module.Finite.trans ℂ _

def reflect (C : Family G) (d : ℕ) : RG17.Free C d →L[ℝ] RG17.Free C d :=
  let A := (Bel C.book).adj (Maxwell.Free.spin_free C.labels) d timeAxis
  LinearMap.toContinuousLinearMap (⟨⟨A,fun x y=>A.map_add x y⟩,fun a b=>by
    change A (a • b)=a • A b
    rw [RCLike.real_smul_eq_coe_smul (K:=ℂ),LinearMap.map_smulₛₗ]; simp⟩)

/-- Differentiate the first position of the actual mixed-degree correlation. -/
theorem column (F : Spec.Final C f V) (J : ℝ → PhysMS.tower V) (d : ℕ) (a : Axis)
    (v : RG17.Free C d) (w : RG17.Free C (d+1)) {r : ℝ} (hr : 0<r) :
    Points.gradient (0:Fin 2) a (fun z : Points 2=> V.classMoment V ![d,d+1] (r • z)
      (fun i=>J r (![d,d+1] i) (ribbon v w i))) detectors =
      V.classMoment V (fun _:Fin 2=>d+1) (r • detectors)
        ![(r:ℂ) • F.sector.derivatives.deriv d a (J r d v),J r (d+1) w] := by
  let t (i : Fin 2) : V.Tag := ⟨![d,d+1] i,J r _ (ribbon v w i)⟩
  let u := F.sector.derivatives.deriv d a (J r d v)
  let y := J r (d+1) w
  have names : update t 0 (⟨d+1,u⟩ : V.Tag) = fun i : Fin 2=> (⟨d+1,![u,y] i⟩ : V.Tag) := by
    funext i;fin_cases i
    · simp [t,u,y,ribbon,Fin.isValue]
    · simp [t,u,y,ribbon,Fin.isValue];rfl
  have differentiated := WilsonMacroscopicSpatialDerivatives.at_slot F none t hr detectors_in 0 a
  change Points.gradient (0:Fin 2) a (fun z : Points 2=>V.classMoment V ![d,d+1] (r • z)
    (fun i=>J r (![d,d+1] i) (ribbon v w i))) detectors = r • V.useAt V (r • detectors) (update t 0 ⟨d+1,u⟩) at differentiated
  rw [names] at differentiated
  apply differentiated.trans
  let B := linear₂ (V.classMoment V (fun _:Fin 2=>d+1) (r • detectors))
  change r • (B u y)=B ((r:ℂ) • u) y
  rw [map_smul,RCLike.real_smul_eq_coe_smul (K:=ℂ)]; rfl

theorem paid (F : Spec.Final C f V) (J : ℝ → PhysMS.tower V) (P : Pier.Lair.Present F J)
    (d : ℕ) (a : Axis) : ∃ M : ℝ,0≤M ∧ ∀ᶠ r in Trace.Pilot.trail,∀ v : RG17.Free C d,
    ‖(J r (d+1)).symm ((r:ℂ) • F.sector.derivatives.deriv d a (J r d v))‖≤M*‖v‖ := by
  let e := d+1
  let δ := Lenses.margin C e / 2
  have hp : 0<δ := half_pos (Weak.Portfolio.freely (C:=C) e).choose_spec.1
  let dir := Points.direction (0:Fin 2) a
  obtain ⟨c,hc,grad⟩ := WilsonMacroscopicSpatialDerivatives.compact F J P ![d,e] {detectors}
    isCompact_singleton (singleton_subset_iff.mpr detectors_in)
  let B := reflect C e
  let k := δ⁻¹*c*‖B‖*‖dir‖
  have k0 : 0≤k := mul_nonneg (mul_nonneg (mul_nonneg (inv_pos.mpr hp).le hc.le) (ContinuousLinearMap.opNorm_nonneg _)) (norm_nonneg _)
  refine ⟨k,k0,?_⟩
  filter_upwards [grad,Pier.Lair.heights F P e,P.aligned e,RG17.positiveLength] with r g gram aligned rp v
  let j := J r e
  let z := j.symm ((r:ℂ) • F.sector.derivatives.deriv d a (J r d v))
  let D := fun x : Points 2=>V.classMoment V ![d,e] (r • x) (fun i=>J r (![d,e] i) (ribbon v (B z) i))
  have derivative := (g detectors (mem_singleton _) (ribbon v (B z)))
  change ‖fderiv ℝ D detectors‖≤c*(∏ i : Fin 2,‖ribbon v (B z) i‖) at derivative
  rw [Fin.prod_univ_two] at derivative
  change ‖fderiv ℝ D detectors‖≤c*(‖v‖*‖B z‖) at derivative
  have measured := column F J d a v (B z) rp
  have E := Pier.Lair.echo F e z z j (aligned.orient ⟨e,Nat.lt_succ_self _⟩) (r • detectors)
  have read : Pier.Lair.arcPrice F e j (r • detectors) z z = (Points.gradient (0:Fin 2) a D detectors).re := by
    rw [E]
    change _ = (Points.gradient (0:Fin 2) a (fun x : Points 2=> V.classMoment V ![d,d+1] (r • x)
      (fun i=>J r (![d,d+1] i) (ribbon v (B z) i))) detectors).re
    rw [measured]
    congr 1
    apply congrArg (V.classMoment V (fun _:Fin 2=>e) (r • detectors))
    funext i; fin_cases i
    · exact j.apply_symm_apply _
    · rfl
  have lower : δ*‖z‖^2≤(Points.gradient (0:Fin 2) a D detectors).re := (gram.1 z).trans_eq read
  have cap : δ*‖z‖^2≤(c*‖B‖*‖dir‖*‖v‖)*‖z‖ := by
    calc
      _ ≤ (Points.gradient (0:Fin 2) a D detectors).re := lower
      _ ≤ ‖Points.gradient (0:Fin 2) a D detectors‖ := (le_abs_self _).trans (Complex.abs_re_le_norm _)
      _ ≤ ‖fderiv ℝ D detectors‖*‖dir‖ := (fderiv ℝ D detectors).le_opNorm _
      _ ≤ (c*(‖v‖*(‖B‖*‖z‖)))*‖dir‖ := mul_le_mul_of_nonneg_right
        (derivative.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (B.le_opNorm z) (norm_nonneg _)) hc.le)) (norm_nonneg _)
      _ = _ := by ring
  by_cases hz : z=0
  · change ‖z‖≤k*‖v‖;rw [hz,norm_zero];exact mul_nonneg k0 (norm_nonneg _)
  have cancel : δ*‖z‖≤c*‖B‖*‖dir‖*‖v‖ := (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hz)).mp (by simpa only [pow_two,mul_assoc] using cap)
  change ‖z‖≤k*‖v‖
  calc
    _ = δ⁻¹*(δ*‖z‖) := by rw [←mul_assoc,inv_mul_cancel₀ hp.ne',one_mul]
    _ ≤ δ⁻¹*(c*‖B‖*‖dir‖*‖v‖) := mul_le_mul_of_nonneg_left cancel (inv_pos.mpr hp).le
    _ = _ := by dsimp only [k];ring

end YM.Integration.WilsonMacroscopicDescendant
