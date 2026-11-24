import YM.Integration.WilsonMaxwellThermometerFaces
import YangMills.WilsonProof.NativeSupport.YM.Next.MAXWELL.Ends

/-! The seven face readings of the original continuum thermometer, linear in
its upper polynomial and integrated on the actual diagnostic profile. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerProfile
open Set Function MeasureTheory Maxwell Maxwell.Free XSpace XSpace.Cirrus XSpace.Normalize
open XSpace.Graph3 XSpace.Rose WilsonMaxwellThermometerFaces
open scoped BigOperators Topology Classical
variable {G : Gauge}

def upper (x : Points 3) (p q : WickPol G) : WickPol G →ₗ[ℂ] ℂ :=
  (Wick.moment G x).toLinearMap (trip 1 p q) 0

private theorem applies (x : Points 3) (u p q : WickPol G) :
    upper x p q u = Wick.moment G x (trip u p q) := by
  rw [upper, MultilinearMap.toLinearMap_apply]
  apply congrArg (Wick.moment G x)
  funext i; fin_cases i <;> simp [trip]

def linked (x : Points 3) (p q : WickPol G) : WickPol G →ₗ[ℂ] ℂ :=
  upper x p q - (upper x 1 q 1) • upper x p 1 - (upper x p 1 1) • upper x 1 q -
    (upper x p q 1) • upper x 1 1 +
    (2 * upper x p 1 1 * upper x 1 q 1) • upper x 1 1

private def packed (x : Points 3) (u p q : WickPol G) (s : Badge) : ℂ :=
  Wick.moment G x (fun i => if i ∈ s then trip u p q i else 1)

private def amount (m : Badge → ℂ) : ℂ :=
  m Finset.univ - (m {0,1}*m {2} + m {0,2}*m {1} + m {1,2}*m {0}) +
    2*m {0}*m {1}*m {2}

private theorem packed_value (x : Points 3) (u p q : WickPol G) (s : Badge) :
    packed x u p q s = upper x (if 1∈s then p else 1) (if 2∈s then q else 1)
      (if 0∈s then u else 1) := by
  rw [applies, packed]; apply congrArg (Wick.moment G x)
  funext i; fin_cases i <;> simp [trip]

private theorem packed_link (x : Points 3) (u p q : WickPol G) :
    linked x p q u = amount (packed x u p q) := by
  simp only [linked, amount, packed_value, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul]
  norm_num [show (0:Fin 3) ≠ 2 by decide, show (1:Fin 3) ≠ 2 by decide,
    show (2:Fin 3) ≠ 1 by decide, show (2:Fin 3) ≠ 0 by decide]
  ring

theorem original (x : Points 3) (u p q : Sec G 6) :
    linked x p.val q.val u.val = connected x (trip u p q) := by
  have hw (s : Badge) : faces x (trip u p q) s = packed x u.val p.val q.val s := by
    change Wick.moment G x (fun i => (missing (trip u p q) s i).val) = _
    unfold packed; apply congrArg (Wick.moment G x)
    funext i; by_cases hi : i ∈ s
    · simp only [missing, hi, if_true]; fin_cases i <;> rfl
    · simp only [missing, hi, if_false]; rfl
  rw [packed_link]; simp only [connected, b3, two_smul, map_add, map_mul, map_sub,
    PowerSeries.constantCoeff_C, hw, amount]; ring

private theorem smooth (p q u : WickPol G) :
    ContinuousOn (fun x : Points 3 => linked x p q u) (conf 3) := by
  intro x hx
  have full (s : Badge) : ContinuousAt (fun y => packed y u p q s) x :=
    (Wick.moment_smooth _ hx).continuousAt
  simp only [packed_link, amount]
  exact ((full _).sub (((full _).mul (full _)).add ((full _).mul (full _)) |>.add
      ((full _).mul (full _)))).add
      (((continuousAt_const.mul (full _)).mul (full _)).mul (full _)) |>.continuousWithinAt

def read {V : Normalize.Store G} (K : Pick V) (p q : WickPol G) : WickPol G →ₗ[ℂ] ℂ where
  toFun u := (Rose.test K).applyTo (fun x => linked x p q u)
  map_add' u v := by
    unfold Test.applyTo
    simp only [map_add, mul_add]
    exact integral_add ((Rose.test K).smearing (smooth p q u)) ((Rose.test K).smearing (smooth p q v))
  map_smul' c u := by
    unfold Test.applyTo
    simp only [map_smul, smul_eq_mul, RingHom.id_apply]
    simp_rw [mul_left_comm _ c]; exact integral_const_mul ..

private theorem commute (o : Ortho) {x : Points 3} (hx : x ∈ conf 3) (u p q : WickPol G) :
    linked (Points.move o x) (reflectPol o p) (reflectPol o q) (reflectPol o u) = linked x p q u := by
  simp only [packed_link]
  apply congrArg amount; funext s
  unfold packed
  have eq : (fun i : Fin 3 => if i∈s then trip (reflectPol o u) (reflectPol o p) (reflectPol o q) i else 1) =
      (fun i => reflectPol o (if i∈s then trip u p q i else 1)) := by
    funext i; by_cases hi : i ∈ s
    · simp only [hi, if_true]; fin_cases i <;> rfl
    · simp only [hi, if_false, map_one]
  rw [eq]; exact moment_rotation x hx _ o

private def positions (o : Ortho) : Points 3 ≃ₗᵢ[ℝ] Points 3 :=
  LinearIsometryEquiv.piLpCongrRight 2 fun _ => o.motion

theorem invariant {V : Normalize.Store G} (K : Pick V) (o : Ortho) (p q u : WickPol G) :
    read K (reflectPol o p) (reflectPol o q) (reflectPol o u) = read K p q u := by
  let F (x : Points 3) := (Rose.test K) x * linked x (reflectPol o p) (reflectPol o q) (reflectPol o u)
  change ∫ x, F x = ∫ x, (Rose.test K) x * linked x p q u
  rw [← (positions o).measurePreserving.integral_comp
    (positions o).toHomeomorph.toMeasurableEquiv.measurableEmbedding F]
  apply integral_congr_ae
  filter_upwards with x
  have pr : (Rose.test K) (positions o x) = (Rose.test K) x := by
    exact congrArg Complex.ofReal (K.spins o.motion x)
  unfold F; rw [pr]
  by_cases hx : x ∈ conf 3
  · exact congrArg ((Rose.test K) x * ·) (commute o hx u p q)
  · rw [(Rose.test K).vanishes hx, zero_mul, zero_mul]

def paired {V : Normalize.Store G} (K : Pick V) (p q : WickPol G) (j l : ℕ) :
    Flavor j →ₗ[ℝ] Flavor l →ₗ[ℝ] ℂ :=
  LinearMap.mk₂ ℝ (fun a b => read K p q (team G a b))
    (by intro a a' b; rw [team_add, map_add])
    (by intro c a b; rw [team_smul, (read K p q).map_smul_of_tower])
    (by intro a b b'; rw [team_swap, team_add, map_add, team_swap G b, team_swap G b'])
    (by intro c a b; rw [team_swap, team_smul, team_swap G b, (read K p q).map_smul_of_tower])

theorem paired_rotates {V : Normalize.Store G} (K : Pick V) (o : Ortho) (p q : WickPol G)
    (hp : reflectPol o p = p) (hq : reflectPol o q = q) {j l : ℕ} (a : Flavor j) (b : Flavor l) :
    paired K p q j l (actFlavor o j a) (actFlavor o l b) = paired K p q j l a b := by
  change read K p q (team G (actFlavor o j a) (actFlavor o l b)) = read K p q (team G a b)
  rw [← orient_team]
  simpa only [hp, hq] using invariant K o p q (team G a b)

end YM.Integration.WilsonMaxwellThermometerProfile
