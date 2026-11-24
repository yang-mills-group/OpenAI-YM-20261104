import YM.Integration.WilsonPhysicalMarkedDefectInteriorSection
import YM.Integration.PhysicalWilsonHotIntegral

/-! The failed part of the actual stored section, *after* division by an
arbitrarily prescribed number of hard allowances, passed along the genuine
positive Wilson history to any earlier reporting scale. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalMarkedDefect.InteriorHot
open Function Filter Set Finset MeasureTheory Lattice Wilson RG OPE.Therm
open IterationFour PhysicalNext.Repeat.Legato Push.AbsoluteSums.Animals
open Extra.Multi RG16.Literal Pert.Asymptotics Trace.Physical.GermGraph
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G) (hG : G.Simple) (therm : Poetry R.family.path.levels)
local notation "C" => R.family
local notation "A" => R.family.path.rep
local notation "κ" => R.family.path.levels.clock.forcedAllowance
local notation "μ" => scene R.family.path

private theorem hot_iff {n : Side} (t : ℝ) (X : Support n) (U : Config G n) :
    U ∈ SelectedCofactorAnchoredRegister.hot t X ↔ ¬ Healthy t X U := by
  change (∃ z ∈ X, z ∈ flags t U) ↔ ¬ Disjoint X (flags t U)
  rw [Finset.not_disjoint_iff]

include hG therm
theorem divided (Qmax : ℕ) :
    ∀ᶠ b : ℕ in atTop, ∀ N, b≤N → ∀ p h (Q : store C h p b) (fee : ℝ),
      ((C).labels.level h).coeffSize Q.x ≤ fee → ∀ q≤Qmax, ∀ j (hj : j≤b),
      ∫ U, ‖actualTransport C (N:=N) (p:=p)
        (fun V => ((Real.sqrt (κ b))^q)⁻¹ • StoredInterior.failed C N p h b Q V) hj U‖ ∂μ N p j ≤
        InteriorSection.roughFee C N p h b fee *
        ((((C).localSection h).footprint (0 : Site ((C).side b p))).card * ballCost 2 * Fintype.card PlaqAxes : ℕ) * κ b := by
  filter_upwards [PhysicalWilsonHotIntegral.divided R hG therm (ρ:=1) zero_lt_one Qmax] with b hp N hb p h Q fee bill q hq j hj
  let X := ((C).localSection h).footprint (0 : Site ((C).side b p))
  let E := SelectedCofactorAnchoredRegister.hot (G:=G) (A N p b).p.threshold X
  let f := fun U => -StoredInterior.fitted C N p h b Q U
  have fm : Measurable f := by
    have eq := funext (StoredInterior.primary C N p h b R.makes hb Q)
    have hd : Continuous (StoredInterior.fitted C N p h b Q) := by
      rw [← eq]
      exact ((C).localSection h).continuous_places _ _
    exact hd.neg.measurable
  have cost : ∀ U ∈ E, ‖f U‖ ≤ InteriorSection.roughFee C N p h b fee := by
    intro U _
    simpa [f] using InteriorSection.rough C N p h b R.makes hb Q bill U
  have pos := (norm_nonneg _).trans (InteriorSection.rough C N p h b R.makes hb Q bill (fun _ => 1))
  have hrestrict : PhysicalWilsonHotIntegral.restricted (E:=E) ((Real.sqrt (κ b))^q)⁻¹ f =
      fun U => ((Real.sqrt (κ b))^q)⁻¹ • StoredInterior.failed C N p h b Q U := by
    funext U
    by_cases ha : U ∈ E
    · have bad := (hot_iff (A N p b).p.threshold X U).1 ha
      dsimp only [X] at bad
      simp [PhysicalWilsonHotIntegral.restricted,ha,StoredInterior.failed,bad,f]
    · have ok : Healthy (A N p b).p.threshold X U := by
        by_contra bad
        exact ha ((hot_iff _ _ _).2 bad)
      dsimp only [X] at ok
      simp [PhysicalWilsonHotIntegral.restricted,ha,StoredInterior.failed,ok]
  have answer := hp N hb p X E (SelectedCofactorAnchoredRegister.measurable _ _) (by simp [E]) q hq _ pos f fm cost j hj
  rw [hrestrict] at answer
  exact answer

/-- One threshold, chosen before the regulated torus, all current physical
coefficients, every divided load up to Qmax, and every earlier Wilson stop. -/
theorem all_orders (h Qmax r : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ b : ℕ in atTop, ∀ N, b≤N → ∀ p (Q : store C h p b) (fee : ℝ),
      ((C).labels.level h).coeffSize Q.x ≤ fee → ∀ q≤Qmax, ∀ j (hj : j≤b),
      ∫ U, ‖actualTransport C (N:=N) (p:=p)
        (fun V => ((Real.sqrt (κ b))^q)⁻¹ • StoredInterior.failed C N p h b Q V) hj U‖ ∂μ N p j
        ≤ ε * fee * regulatorRun C N p b ^ r := by
  let e := BasisCost.slots ((C).labels.level h)
  let P := BasisCost.price ((C).localSection h)
  let T := ((C).localSection h).stencil.card * ballCost 2 * Fintype.card PlaqAxes
  let B := P * (2:ℝ)^e * T
  have pp : 0≤P := zero_le_one.trans (BasisCost.price_pos _)
  have bp : 0≤B := mul_nonneg (mul_nonneg pp (by positivity)) (Nat.cast_nonneg T)
  have dp : 0<1+B := by linarith
  filter_upwards [divided R hG therm Qmax,OriginalForcedFlat.allowance R hG (r+e) (div_pos hε dp)] with b priced flat N hb p Q fee bill q hq j hj
  let g := regulatorRun C N p b
  have gp : 0<g := g_pos R.makes hb
  have fp : 0≤fee := (Finset.sum_nonneg fun _ _ => norm_nonneg _).trans bill
  have X : (((C).localSection h).footprint (0 : Site ((C).side b p))).card * ballCost 2 * Fintype.card PlaqAxes ≤ T :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ Finset.card_image_le)
  have rp : 0 ≤ InteriorSection.roughFee C N p h b fee := by
    unfold InteriorSection.roughFee
    exact mul_nonneg (mul_nonneg pp (pow_nonneg (inv_nonneg.mpr (by linarith : 0 ≤ g/2)) _)) fp
  refine ((priced N hb p h Q fee bill q hq j hj).trans ?_)
  calc
    _ ≤ InteriorSection.roughFee C N p h b fee * (T:ℝ) * κ b :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by exact_mod_cast X) rp) (Real.exp_nonneg _)
    _ ≤ InteriorSection.roughFee C N p h b fee * (T:ℝ) * (ε/(1+B)*g^(r+e)) :=
      mul_le_mul_of_nonneg_left (flat N p hb) (mul_nonneg rp (Nat.cast_nonneg _))
    _ = (B/(1+B))*(ε*fee*g^r) := by
      change P*(g/2)⁻¹^e*fee*T*(ε/(1+B)*g^(r+e))=(B/(1+B))*(ε*fee*g^r)
      rw [pow_add,inv_div,div_pow]
      dsimp only [B]
      field_simp [gp.ne']
    _ ≤ ε*fee*g^r := mul_le_of_le_one_left (by positivity) ((div_le_iff₀ dp).2 (by linarith))

end YM.Integration.WilsonPhysicalMarkedDefect.InteriorHot
