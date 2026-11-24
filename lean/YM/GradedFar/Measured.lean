import YM.GradedFar.Bound
import YM.GradedFar.Joint
import YM.Integration.WilsonPositionHomogeneousFrame

/-!
# The second line of (M.2), at the measured coupling
-/
namespace YM.FVA2.GradedFar
noncomputable section
open Filter Function Real Set
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open Integration.WilsonPositionHomogeneousFrame
open scoped Topology BigOperators Classical

variable {G : Gauge} {n m : ℕ} {N : YM.FVA2.Register.WilsonPrescription G}
  {M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
  {simple : G.Simple} {A : Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
  {K : Set (Points n)} {S : Set (Points m)}
  {R : PhysicalNext.Repeat.Legato.Run G} {f : Extraction.Order} {P : Table R.family.book}
  (U : Spec.Final R.family f P) (J : ℝ → PhysMS.tower P)

local notation "θ" => reading U J N
local notation "g" => gYM G
open Trace.Pilot (trail)

/-- One can use this other sufficient PoseFit (F.3) *tested* hypothesis
with the same construction's test and sign. Check the denominator division,
rather than changing the observable. -/
theorem calibrationTest (proxy : ℝ → ℝ) (B : ℝ) (k : ℕ)
    (hf : ∀ᶠ r in trail,
        ‖Integration.WilsonPositionThermometerReading.tested U
            (Integration.WilsonPositionPrescribedFrame.positioned U J N.store) N.criterion r -
          ((Rose.cT N.criterion.cut G N.criterion.image * proxy r:ℝ):ℂ)‖ ≤ B * g r ^ k) :
    ∀ᶠ r in trail, |θ r - proxy r| ≤
      B / |Rose.cT N.criterion.cut G N.criterion.image| * g r ^ k := by
  let m := (Rose.cT N.criterion.cut G N.criterion.image)
  have hm : 0 < |m| := abs_pos.mpr N.criterion.fresh.ne
  let z := Integration.WilsonPositionThermometerReading.tested U
    (Integration.WilsonPositionPrescribedFrame.positioned U J N.store) N.criterion
  filter_upwards [hf] with r hr
  have he : ((z r)-((m*proxy r:ℝ):ℂ)).re = m*(θ r-proxy r) := by
    rw [Complex.sub_re,Complex.ofReal_re,mul_sub,show m*θ r=(z r).re from
      Integration.WilsonPositionThermometerReading.calibrated_denominator U _ _ _]
  have h := (Complex.abs_re_le_norm ((z r)-((m*proxy r:ℝ):ℂ))).trans hr
  rw [he,abs_mul,mul_comm |m|] at h
  change _ ≤ B / |m| * g r ^ k
  exact ((le_div_iff₀ hm).mpr h).trans_eq (by ring)

include H
/-- FormalDemand to second (M.2), in the precise operands of the supplied proof.
As in it the estimate is under the hypotheses of PoseFit, RoundMeter, etc.; here
only the (physical) calibration hypotheses actually needed have to be supplied.
This entry takes specifically the PoseFit (F.3) and `t'_ℓ ∼ g` hypotheses; no
inputs involving the OPE, dilation, spatial or grade or crop estimates needed
other than buying exactly the one original `Match`. `proxy`=`t'_ℓ`, use with
`k+1=M` at any sufficiently high calibration booking.

The coupling in the series evaluation is READ on the actual physical hierarchy,
with the actual positioned frame, ROSE input, all proper faces, never `proxy`.
Arbitrary moving T above the sufficiently large threshold T₀ (so also in the
stated M.1 range). Uniform even among the entire field-label balls (L,R'=1;
or any fixed radius in the coordinate sup norm), center-relative positions in
these arbitrary fixed compacta. Does not involve any other viewer (works with
any of them subsequently; the formal series and the measured t do not vary).
Built from the pin §F's prescription (use H at B's election). -/
theorem second (proxy : ℝ → ℝ)
    (hproxy : Tendsto (fun r : ℝ => proxy r / g r) trail (𝓝 1)) (k : ℕ) (hk : 2 ≤ k) (B : ℝ)
    (hF3 : ∀ᶠ r in trail, |θ r - proxy r| ≤ B * g r ^ k)
    (hK : IsCompact K) (hx : K ⊆ conf n) (hS : IsCompact S) (hy : S ⊆ O.Enh.Outside m)
    (d : Fin n → ℕ) (e : Fin m → ℕ) (L R' : ℝ) (p h : ℕ) :
    (∀ᶠ r in trail, 0 < g r ∧ 0 < θ r ∧ |θ r| ≤ 1 ∧ |θ r| ≤ 2*g r) ∧
    ∃ C : ℝ, 0 < C ∧ ∃ a : ℕ, ∃ T₀ : ℝ, 2 ≤ T₀ ∧
      ∀ᶠ r in trail, ∀ T ≥ T₀, ∀ x ∈ K, ∀ y ∈ S,
        ∀ u : Inputs G d, Within L u → ∀ v : Inputs G e, Within R' v →
          ‖crop p (θ r) (Yx N M x y u v (log T)) -
            crop p (θ r) (Dx N M y v (log T) (cActual N x u h p (θ r)))‖ ≤
            C * (T⁻¹^(h+1) + g r^(p+1)) * (1+log T)^a := by
  have hr := relative_reading simple θ proxy hproxy k hk B hF3
  exact ⟨paid_reading simple θ hr, paid H hK hx hS hy d e L R' p h θ hr⟩
end
end YM.FVA2.GradedFar
