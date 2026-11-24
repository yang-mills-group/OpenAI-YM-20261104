import YM.Integration.WilsonMacroscopicRichPositionRows
import YM.Integration.WilsonMacroscopicRichMSCoefficient
import YM.Integration.WilsonThermometerWeakPairClock

/-! A running positive output is determined by the original two-site exterior observations at
a polynomially larger radius. The inverse acts on the entire true filtered field space. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPublicOutputDetector
open Filter Function Set Table Spec OPE OPE.Orbits PhysMS Trace.Pilot Climb
open FVA2 FVA2.Register PhysicalNext.Repeat.Legato
open WilsonMatrixTicketLanesSmearedPivot WilsonMacroscopicRichPositionRows
open scoped Classical Topology BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) (J : ℝ → tower S) (Z : WilsonPrescription G)

private lemma price {u : ℝ} (up : 0 < u) (A h : ℕ) :
    ((u ^ A) ^ 2) ^ (-(h : ℝ) - (1 / 2 : ℝ)) = (u ^ (A * (2*h+1)))⁻¹ := by
  have p := pow_pos up A
  rw [← Real.rpow_natCast (u ^ A) 2, ← Real.rpow_mul p.le,
    show ((2 : ℕ) : ℝ) * (-(h : ℝ) - 1/2) = -((2*h+1 : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_neg p.le, Real.rpow_natCast, pow_mul]

/-- Choose the actual detector before the inner and outer radii. The second term can be
split into signed ordinary measurements on the same probes. -/
theorem original {Y : (Bel R.family.book).Hierarchy}
    (lead : Leading F J) (owed : ∀ d, ∀ᶠ r in trail, Frame.obedient F Y (J r) d)
    (simple : G.Simple) (h : ℕ) :
    ∃ B : Profiles R h, ∃ w : B.probes.index → Atom (R:=R) h,
      ∃ issued : ∀ j, B.probes.shell j = WilsonMatrixTicketLanesTwoSites.shell R.family.book.grid h (w j),
      ∃ K : ℝ, 0 ≤ K ∧ ∀ (g : ℝ → ℝ), Coupling G g → ∀ A : ℕ, ∀ᶠ r in trail,
      let t := r / ((g r)^A)^2
      ∃ tp : 0 < t, ∀ (n : ℕ) (x : Points n) (v : Fin n → (Bel R.family.book).Tag) (y z : S.Field h),
        let observed := sample F J Z B w issued tp r x v
        (g r)^(A*(2*h+1)) * ‖(J r h).symm (y-z)‖ ≤
          K * (‖row F J Z B t y - observed‖ + ‖observed - row F J Z B t z‖) := by
  obtain ⟨B,two,paid⟩ := WilsonMacroscopicRichTwoDatePivot.original F J Z lead owed simple h
  choose w issued using two
  obtain ⟨K,kp,decoder⟩ := paid (1/2) (by norm_num)
  refine ⟨B,w,issued,K,kp,?_⟩
  intro g hg A
  have tends : Tendsto (fun r => r / ((g r)^A)^2) trail trail := by
    have eq : (fun r => r / ((g r)^A)^2) = WilsonThermometerWeakPairClock.scale g (A*2) :=
      funext fun r => by rw [WilsonThermometerWeakPairClock.scale, pow_mul]
    rw [eq]
    exact WilsonThermometerWeakPairClock.small simple g hg (A*2)
  filter_upwards [tends.eventually decoder, hg.positive, length_rate.pos,
    (hg.conforms simple).eventually (ge_mem_nhds zero_lt_one)] with r read gp rp cap
  intro t
  have sp := pow_pos (pow_pos gp A) 2
  have room : ((g r)^A)^2 ∈ Ioc (0:ℝ) 1 :=
    ⟨sp, pow_le_one₀ (pow_nonneg gp.le _) (pow_le_one₀ gp.le cap)⟩
  have eq : ((g r)^A)^2 * t = r := by dsimp only [t]; field_simp [sp.ne']
  refine ⟨div_pos rp sp,?_⟩
  intro n x v y z observed
  have bound := read _ room (y-z)
  rw [eq, price gp A h, (row F J Z B t).map_sub] at bound
  have wp := pow_pos gp (A*(2*h+1))
  calc
    _ ≤ (g r)^(A*(2*h+1)) * (K * ((g r)^(A*(2*h+1)))⁻¹ *
          ‖row F J Z B t y - row F J Z B t z‖) :=
      mul_le_mul_of_nonneg_left bound wp.le
    _ = K * ‖row F J Z B t y - row F J Z B t z‖ := by field_simp [wp.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left (norm_sub_le_norm_sub_add_norm_sub _ observed _) kp

/-- The slack from the sharp spatial power survives the inverse even at the top grade. -/
theorem powers {u err K C D : ℝ} (up : 0 < u) (cap : u ≤ 1)
    (kp : 0 ≤ K) (cp : 0 ≤ C) (P E A h : ℕ) (room : P+E ≤ A)
    (paid : u^(A*(2*h+1)) * err ≤
      K * (C * ((u^A)^2)^(h+1) / u^E + D * u^(P+A*(2*h+1)))) :
    err ≤ K * (C+D) * u^P := by
  let W := A*(2*h+1)
  have pos := pow_pos up W
  have cut : ((u^A)^2)^(h+1) = u^W * u^A := by
    rw [← pow_mul, ← pow_mul, ← pow_add]
    congr 1
  have cheap : u^A / u^E ≤ u^P :=
    (div_le_iff₀ (pow_pos up E)).mpr (by rw [←pow_add]; exact pow_le_pow_of_le_one up.le cap room)
  apply le_of_mul_le_mul_left (a:=u^W) _ pos
  calc
    _ ≤ K * (C * ((u^A)^2)^(h+1) / u^E + D * u^(P+W)) := paid
    _ = K * (C * (u^A / u^E) * u^W + D * u^P * u^W) := by rw [cut,pow_add]; ring
    _ ≤ K * (C * u^P * u^W + D * u^P * u^W) :=
      mul_le_mul_of_nonneg_left (add_le_add_left (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left cheap cp) pos.le) _) kp
    _ = _ := by ring
end YM.Integration.WilsonPublicOutputDetector
