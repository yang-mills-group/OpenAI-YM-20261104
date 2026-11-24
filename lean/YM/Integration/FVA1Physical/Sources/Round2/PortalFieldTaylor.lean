import YM.Integration.FVA1Physical.Sources.Round2.ClipRows
import YM.Integration.FVA1Physical.Sources.Round2.SchurWickRows

/-! Taylor-expand only the literal inserted physical fields inside the real conditional
Haar orbit. The full interacting action, chart Jacobian, cut and denominator are kept
on both sides. The constants are uniform in the period and in the exterior. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1800000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Function Filter Set Finset MeasureTheory Lattice RG YM.Wilson Tree Precision Exterior Pressure
open RGComparison.Core16 RGComparison.Core16.Spool RGComparison.Core16.Lumen
open MSbar MSbar.Heath MSbar.Heath.Cottage MSbar.Heath.Stock MSbar.Bakery MSbar.Bakery.Film
open MSbar.Cacao MSbar.Whisk Push.Uniform Next.SectorChange YM.Integration.FVA1Physical.Wilson
open Further.GaussianScalar
open scoped Classical Topology BigOperators
variable {G : Gauge} {ι : Type} [Fintype ι] (J : ι→Lamp G)
variable {c f : Side} (S : StepData c f) (F : Forest S.ratio) (o : ι→Site f)
variable (X : Support f) (live : ∀ i,slotEdge J S F o i∈board F X)

def fieldTaylor (m : SpaceP F X G) (g : ℝ) (part : Bool) (n : ℕ) (w : SpaceP F X G) : ℝ :=
  let s:=slotPrices J S F o X live
  ∑ k∈Finset.range (n+1),g^k*MvPolynomial.eval (fun i=>g⁻¹*m (s i)+w (s i)) (lampRow J part (activeSlots J S F o) k)

theorem fieldTaylor_cont (m : SpaceP F X G) (g : ℝ) (part : Bool) (n : ℕ) :
    Continuous (fieldTaylor J S F o X live m g part n) := by
  let s:=slotPrices J S F o X live
  have h : Continuous (fun w : SpaceP F X G => fun i=>g⁻¹*m (s i)+w (s i)) :=
    continuous_pi fun i=>continuous_const.add (continuous_apply (s i))
  exact continuous_finsetSum _ (fun k _=>continuous_const.mul ((MvPolynomial.continuous_eval _).comp h))

/-- The coefficient integrals still carry the full exponential conditional weight. -/
def tiltedTaylor (Y : Support f) (A : Set (Config G f)) (χ : ChartRatio G) (m : SpaceP F X G)
    (B : Matrix (Lake F X G) (Lake F X G) ℝ) (g : ℝ) (E : Config G f → ℝ)
    (U : Config G f) (part : Bool) (n : ℕ) : ℝ :=
  let den:=gaussianMass F X Y A χ m B g E 1 U
  if den=0 then look part (tally J o 1)
  else (∫ w, Portal.purse (clipM F X Y A χ g m U) (fun u=>fLog F X χ g u m U E B) w *
        fieldTaylor J S F o X live m g part n w ∂fieldLaw B)/den

theorem held_field_taylor (part : Bool) (n : ℕ) :
    ∃ δ C:ℝ, 0<δ ∧ 0≤C ∧ ∀ {c f : Side} (S : StepData c f) (F : Forest S.ratio)
      (o : ι→Site f) (X Y : Support f) (live : ∀ i,slotEdge J S F o i∈board F X)
      (V : Voice G) (_ : Clear G V) (O : Config G c) (U : Config G f)
      (ν : Positions (Key F G)) (χ : ChartRatio G) (_ : LocalRatio χ) (v : F.Free→G.Color)
      {a b K H M g : ℝ} (_ : Couch V F ν Y χ v O a b K H M) (_ : X⊆Y)
      (m : SpaceP F X G) (B : Matrix (Lake F X G) (Lake F X G) ℝ) (E : Config G f→ℝ),
      0<g → 3*shade G*K≤δ →
      let A:=hotel F X Y V O ν a b
      |gaussianOrbit F X Y A χ m B g E (fun Z=>look part (tally J o Z)) U -
          tiltedTaylor J S F o X live Y A χ m B g E U part n| ≤ C*(3*shade G*K)^(n+1) := by
  obtain ⟨δ,C,hδ,hC,price⟩:=drawn_remainder J part n
  refine ⟨δ,C,hδ,hC,?_⟩
  intro c f S F o X Y live V clear O U ν χ hχ v a b K H M g paid xy m B E hg room A
  let s:=slotPrices J S F o X live
  let ρ:=Portal.purse (clipM F X Y A χ g m U) (fun u=>fLog F X χ g u m U E B)
  have hK : 0≤K:= le_trans (add_nonneg (norm_nonneg _) (paid.glued.le.trans paid.lifts)) paid.ht
  have hrate : 0≤3*shade G*K:= mul_nonneg (mul_nonneg (by norm_num) (shade_pos G).le) hK
  have hρ (w : SpaceP F X G) : 0≤ρ w:= by
    exact Set.indicator_nonneg (fun _ _=>(Real.exp_pos _).le) _
  have support (w : SpaceP F X G) (h : ρ w≠0) : w∈clipM F X Y A χ g m U := by
    by_contra outside;apply h;exact Set.indicator_of_notMem outside _
  have perp : Measurable (draw F X U m g):= (mspec F X U).comp ((release_continuous
    (orbitJ F X U)).measurable.comp (tape.measurable.comp ((show Continuous (fun w : SpaceP F X G=>m+g•w) by fun_prop).measurable)))
  have den : gaussianMass F X Y A χ m B g E 1 U= ∫ w,ρ w ∂fieldLaw B := by
    simp only [gaussianMass,Pi.one_apply,mul_one,ρ]
  unfold gaussianOrbit tiltedTaylor
  by_cases empty : gaussianMass F X Y A χ m B g E 1 U=0
  · simp only [empty,if_true,sub_self,abs_zero];exact mul_nonneg hC (pow_nonneg hrate _)
  simp only [if_neg empty]
  rw [den]
  obtain ⟨hm,_,keep⟩:=encouraging J
  apply common_mass_sub (fieldLaw B) ρ (fun w=>look part (tally J o (draw F X U m g w)))
    (fieldTaylor J S F o X live m g part n) hρ (((look part).continuous.comp (tally_cont J o)).measurable.comp perp)
    (fieldTaylor_cont J S F o X live m g part n).measurable (mul_nonneg hC (pow_nonneg hrate _))
  · intro w _;rw [←exhibition J o];exact keep part _
  intro w hw
  let q:=fun i=>g⁻¹*m (s i)+w (s i)
  have gs : g • Lumen.vector q = fun i=>tape (G:=G) (m+g•w) (⟨slotEdge J S F o i,live i⟩) := by
    funext i;apply PiLp.ext;intro k
    change g*(g⁻¹*m (s (i,k))+w (s (i,k)))=m (s (i,k))+g*w (s (i,k))
    rw [mul_add,←mul_assoc,mul_inv_cancel₀ hg.ne',one_mul]
  have cap : g*‖Lumen.vector q‖≤3*shade G*K:=by
    rw [←norm_smul_of_nonneg hg.le,gs]
    exact (pi_norm_le_iff_of_nonneg hrate).mpr fun i=>drawn_log_cap F V X Y O U ν χ hχ clear v paid xy m w (support w hw) ⟨_,live i⟩
  have fixed:=price S F o X live U m w g hg (cap.trans room)
  rw [←Real.norm_eq_abs]
  exact fixed.trans ((le_of_eq (by rw [mul_pow];ring :
    C*‖Lumen.vector q‖^(n+1)*g^(n+1)=C*(g*‖Lumen.vector q‖)^(n+1))).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg hg.le (norm_nonneg _)) cap _) hC))

end YM.Integration.FVA1Physical.Round2.Curvature
