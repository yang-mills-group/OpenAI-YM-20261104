import YM.Integration.WilsonReportingWindowRoom
import YM.RG16.Unmasked.Purchased

/-! The genuine physical moving-frame labels fit one reporting allowance,
uniformly on all subsequent radii, unit field tests and finite regulators. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalMasterRoom
open Function Set Filter Lattice RG Wilson Spec OPE OPE.Orbits Climb PhysMS Trace.Pilot
open MergeProof MergeProof.Accent MergeProof.Ribbons Source Overlay Bid ManyCopies
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow Bandage Extra.Histories
open RG16 RG16.Literal Trace.Physical.GermGraph WilsonMasterReportingWords
open scoped Classical Topology BigOperators
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}

def rateFactor (C : Family G) (e m : ℕ) : ℝ :=
  ((2:ℝ)^(degree (C.labels.level e))*2)*fly C.path.levels e m / plumR C e 1 m

theorem factor (hG : G.Simple) (e : ℕ) :
    RateIs atTop C.S.scale (rateFactor C e) (e:ℝ) := by
  have shape := plumN C e hG 1 one_pos
  have denominator : RateIs atTop C.S.scale (plumR C e 1) (-(e:ℝ)) :=
    ⟨Eventually.of_forall shape.pos,shape.pitch⟩
  have flyRate' := flyRate hG (normal_height C) e
  have cap := RateIs.const (c:=(2:ℝ)^(degree (C.labels.level e))*2) C.S.divergent
    (show (0:ℝ) < 2^(degree (C.labels.level e))*2 by positivity)
  exact ((cap.mul flyRate').div denominator).swap (by ring)

variable (F : Spec.Final C f S) (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → tower S) (H : Leading F J)

def projection (e d : ℕ) (r : ℝ) :
    (Bel C.book).Field d →L[ℂ] S.Field e :=
  Frame.pulling d J (LinearMap.toContinuousLinearMap (R.cutTest e d)) r

def labelSize (e d : ℕ) (r : ℝ) : ℝ :=
  (∑ k : (C.labels.level e).Index,
    ‖(ContinuousLinearMap.proj k) ∘L (S.representative e).toContinuousLinearMap‖) *
    ‖projection F R J e d r‖

theorem row (e d : ℕ) (r : ℝ) (v : (Bel C.book).Field d) (hv : ‖v‖ ≤ 1) :
    (C.labels.level e).coeffSize (S.representative e (R.cutTest e d (J r d v))) ≤
      labelSize F R J e d r := by
  unfold labelSize Labels.Frame.coeffSize
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k _
  let L : S.Field e →L[ℂ] ℂ := (ContinuousLinearMap.proj k) ∘L (S.representative e).toContinuousLinearMap
  let P := projection F R J e d r
  change ‖L (P v)‖ ≤ ‖L‖*‖P‖
  apply (L.le_opNorm _).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg L)
  exact (P.le_opNorm v).trans ((mul_le_mul_of_nonneg_left hv (norm_nonneg P)).trans_eq (mul_one _))

include H in
theorem order (e d : ℕ) (he : e ≤ d) :
    RateLE trail LogV (labelSize F R J e d) (-(e:ℝ)) := by
  let p := LinearMap.toContinuousLinearMap (R.cutTest e d)
  have measured := Frame.upper F d J H e he p ?_
  swap
  · cases e with
    | zero => intro y hy; rw [show y=0 from (Submodule.mem_bot ..).mp hy,map_zero]
    | succ e => intro y hy; obtain ⟨u,rfl⟩ := hy
                change R.cutTest (e+1) d _ = 0
                rw [R.cut_rise]
                exact R.kills_lower _ _ (Nat.lt_add_one _) _
  have bounds := (RateLE.const
    (∑ k : (C.labels.level e).Index,
      ‖(ContinuousLinearMap.proj k) ∘L (S.representative e).toContinuousLinearMap‖)
    PhysMS.to_log_zoom).mul (RateLE.norm (X:=(Bel C.book).Field d →L[ℂ] S.Field e) measured)
  intro a ha
  filter_upwards [bounds a (by simpa only [zero_add] using ha)] with r priced
  exact priced

include H in
/-- All true source tests in the unit ball, every allowed reporting radius,
and every later cutoff and period share this single numerical allowance. -/
theorem purchased (hG : G.Simple) (e d : ℕ) (he : e ≤ d) (B : ℝ) :
    ∃ A : ℕ → ℝ, RateIs atTop C.S.scale A 0 ∧ ∀ᶠ m in atTop,
      ∀ r ∈ Icc (C.S.a m) (WilsonReportingLength.radius C B m),
      ∀ N p (hm : m < N) (op : Opened C e m p)
      (v : (Bel C.book).Field d), ‖v‖ ≤ 1 →
        (C.labels.level e).coeffSize (coordinates F.room.cutoff N p e m op hm.le
          (S.representative e (R.cutTest e d (J r d v)))) ≤ A m := by
  let z (r : ℝ) := (r^e)⁻¹ * labelSize F R J e d r
  have unscaled : RateLE trail LogV z 0 := by
    have normalized := ((PhysMS.length_rate.power e).inv.pays PhysMS.to_log_zoom).mul
      (order F R J H e d he)
    exact normalized.mono (by simp)
  let env := WilsonReportingWindowRoom.envelope C B z
  obtain ⟨envRate,window⟩ := WilsonReportingWindowRoom.uniform C B unscaled
  let M (m : ℕ) := env m*(WilsonReportingLength.radius C B m)^e + (C.S.a m)^e
  have payload : RateIs atTop C.S.scale M (-(e:ℝ)) := by
    have radius := (WilsonReportingLength.radius_rate C B).power e
    have mesh := (normal_height C).mesh.power e
    exact (((envRate.mul radius).add mesh C.S.divergent).swap (by simp))
  refine ⟨fun m => rateFactor C e m*M m,((factor hG e).mul payload).swap (by ring),?_⟩
  filter_upwards [window,envRate.pos,(factor (C:=C) hG e).pos] with m financed envPos factorPos
  intro r hr N p hm op v hv
  have rp := (C.S.a_pos m).trans_le hr.1
  have positive : 0 < r^e := pow_pos rp e
  have w := financed r hr
  have current : labelSize F R J e d r ≤ env m*r^e := by
    apply (div_le_iff₀ positive).mp
    rw [div_eq_inv_mul]
    exact (Real.le_norm_self (z r)).trans w
  have bounded := current.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ rp.le hr.2 _) envPos.le)
  exact (WilsonMasterCoordinatePrice.scaled F.room.cutoff N p e m op hm _).trans
    (mul_le_mul_of_nonneg_left (add_le_add ((row F R J e d r v hv).trans bounded) le_rfl)
      factorPos.le)

end YM.Integration.WilsonPhysicalMasterRoom
