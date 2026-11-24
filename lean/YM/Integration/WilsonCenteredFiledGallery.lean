import YM.Integration.WilsonCenteredCompulsoryPair
import YM.Integration.WilsonCenteredRegularHit

/-! Retain the entire eligible hard inventory while hearing a signed regular
replacement on its original Wilson field. The proper hard faces remain in the
invoice. The quiet, two singletons, pair, and filed counterterm have their
original masks on every configuration. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredFiledGallery
open RG Lattice Wilson Marker QuadraticLocal Ac Extra.Trajectories Comparison.RG02.Cumulants
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {V X ι μ : Type} [DecidableEq V] [Fintype V]
    {R : Census V} {P : Rep G n} {o : V → Site n}
    (L : Lamps X ι G P.p o R) (D : Lamps X μ G P.p o R)
    (K : Hard X P.p P.activities.forced P.activities.K o R)
    (w : V → ℝ) (hw : ∀ i, 0 < w i) {α M δ : ℝ} (width : 0 ≤ α)
    (model : L.Paid w P.p.B α M) (debt : D.Paid w P.p.B α δ)
    (a b c : V) (s : R.Mode) (apart : a ≠ b) (pair : s.val = {a,b})

include hw width model debt apart pair

/-- A comparison on the original unnormalized numerator. The quiet hard
mass can vanish. Its complete mixed face cancels and its two singleton faces
remain at their genuine roots. -/
theorem original (x : X) (U : Config G n) :
    let A : Gallery X (ι ⊕ μ) o P R := ⟨L.join D,K⟩
    let B : Gallery X ι o P R := ⟨L,K⟩
    let T := L.log x U
    let E := D.log x U
    let Z := Poly.pass T
    let Y := Poly.pass (T+E)
    let H := B.gas x U
    let f := R.fire
    let j := (Real.exp (P.exponent U) : ℂ)
    ((A.density x U).part s - (A.density x U).part (f c)) -
        ((B.density x U).part s - (B.density x U).part (f c)) =
      j * (H.part R.quiet * (E.part s - E.part (f c) + E.part (f a)*Y.part (f b)
          + Z.part (f a)*E.part (f b)) + E.part (f a)*H.part (f b)
          + H.part (f a)*E.part (f b)) := by
  intro A B T E Z Y H f j
  have ls := model.sums width hw x U
  have ds := debt.sums width hw x U
  have zT : T.part R.quiet = 0 := Lamps.quiet_of_hasSum x U ls
  have zE : E.part R.quiet = 0 := Lamps.quiet_of_hasSum x U ds
  have zS : (T+E).part R.quiet = 0 := by rw [Poly.part_plus,zT,zE,add_zero]
  have zy : connected Y = T+E := connected_pass zS
  have zz : connected Z = T := connected_pass zT
  have yq : Y.part R.quiet = 1 := Poly.pass_part _ zS
  have zq : Z.part R.quiet = 1 := Poly.pass_part _ zT
  have dlog : connected Y - T = E := by rw [zy,add_sub_cancel_left]
  have first (v : V) : Y.part (f v) - Z.part (f v) = E.part (f v) := by
    rw [← lamp v Y yq, ← lamp v Z zq, zy, zz, Poly.part_plus, add_sub_cancel_left]
  have soft := WilsonCenteredCompensatedPairRate.exact_pair a b c s apart pair Y T yq zT
  rw [dlog] at soft
  have hard := WilsonCenteredCompulsoryPair.original a b c s apart pair Y Z H yq zq
  rw [first a,first b,soft] at hard
  have installed : A.density x U = j • (Y * H) := by
    change j • (Poly.pass ((L.join D).log x U)*H)=_
    rw [Lamps.joinLog x U ls ds]
  rw [installed, show B.density x U = j • (Z*H) from rfl]
  simp only [Poly.part_smul]
  linear_combination j * hard

omit apart in
theorem regular (x : X) (U : Config G n) :
    let T := L.log x U
    let E := D.log x U
    let Z := Poly.pass T
    let Y := Poly.pass (T+E)
    let f := R.fire
    let ea := (w a)⁻¹ * δ
    let eb := (w b)⁻¹ * δ
    let za := (w a)⁻¹ * M
    let yb := (w b)⁻¹ * M + eb
    let soft := (Poly.toll w s)⁻¹ * δ + (w c)⁻¹ * δ + ea*yb + za*eb
    ‖E.part s - E.part (f c) + E.part (f a)*Y.part (f b)
      + Z.part (f a)*E.part (f b)‖ ≤ soft := by
  intro T E Z Y f ea eb za yb soft
  have tq : T.part R.quiet = 0 := Lamps.quiet_of_hasSum x U (model.sums width hw x U)
  have eq : E.part R.quiet = 0 := Lamps.quiet_of_hasSum x U (debt.sums width hw x U)
  have sq : (T+E).part R.quiet = 0 := by rw [Poly.part_plus,tq,eq,add_zero]
  have basis (v : V) : ‖T.part (f v)‖ ≤ (w v)⁻¹ * M := by
    simpa only [Poly.solo_toll] using WilsonCenteredRegularHit.component L w hw width model
      x U (R.fire v) v (Finset.mem_singleton_self v)
  have single (v : V) : ‖E.part (f v)‖ ≤ (w v)⁻¹ * δ := by
    simpa only [Poly.solo_toll] using WilsonCenteredRegularHit.component D w hw width debt
      x U (R.fire v) v (Finset.mem_singleton_self v)
  have mixed : ‖E.part s‖ ≤ (Poly.toll w s)⁻¹ * δ :=
    WilsonCenteredRegularHit.component D w hw width debt x U s a (by simp [pair])
  have Az : Z.part (f a) = T.part (f a) := by
    rw [← lamp a Z (Poly.pass_part T tq), connected_pass tq]
  have By : Y.part (f b) = T.part (f b) + E.part (f b) := by
    rw [← lamp b Y (Poly.pass_part _ sq), connected_pass sq, Poly.part_plus]
  have ha : ‖Z.part (f a)‖ ≤ za := Az ▸ basis a
  have hb : ‖Y.part (f b)‖ ≤ yb := By ▸ (norm_add_le _ _).trans (add_le_add (basis b) (single b))
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · exact (norm_sub_le _ _).trans (add_le_add mixed (single c))
    · rw [norm_mul]; exact mul_le_mul (single a) hb (norm_nonneg _) ((norm_nonneg _).trans (single a))
  · rw [norm_mul]; exact mul_le_mul ha (single b) (norm_nonneg _) ((norm_nonneg _).trans ha)

/-- The rooted signed Taylor fee times the three unsimplified physical hard
faces. All input prices precede the fine field and volume. -/
theorem paid (x : X) (U : Config G n) :
    let A : Gallery X (ι ⊕ μ) o P R := ⟨L.join D,K⟩
    let B : Gallery X ι o P R := ⟨L,K⟩
    let H := B.gas x U
    let f := R.fire
    let ea := (w a)⁻¹ * δ
    let eb := (w b)⁻¹ * δ
    let za := (w a)⁻¹ * M
    let yb := (w b)⁻¹ * M + eb
    let soft := (Poly.toll w s)⁻¹ * δ + (w c)⁻¹ * δ + ea*yb + za*eb
    ‖((A.density x U).part s - (A.density x U).part (f c)) -
       ((B.density x U).part s - (B.density x U).part (f c))‖ ≤
      Real.exp (P.exponent U) *
        (‖H.part R.quiet‖*soft + ea*‖H.part (f b)‖ + ‖H.part (f a)‖*eb) := by
  intro A B H f ea eb za yb soft
  let T := L.log x U
  let E := D.log x U
  let Z := Poly.pass T
  let Y := Poly.pass (T+E)
  have single (v : V) : ‖E.part (f v)‖ ≤ (w v)⁻¹ * δ := by
    simpa only [Poly.solo_toll] using WilsonCenteredRegularHit.component D w hw width debt
      x U (R.fire v) v (Finset.mem_singleton_self v)
  have sb := regular L D w hw width model debt a b c s pair x U
  rw [original L D K w hw width model debt a b c s apart pair x U, norm_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.exp_pos _).le]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul]; exact mul_le_mul_of_nonneg_left sb (norm_nonneg _)
    · rw [norm_mul]; exact mul_le_mul_of_nonneg_right (single a) (norm_nonneg _)
  · rw [norm_mul]; exact mul_le_mul_of_nonneg_left (single b) (norm_nonneg _)

end YM.Integration.WilsonCenteredFiledGallery
