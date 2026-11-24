import YM.Integration.WilsonOrdinaryPivotAsymptotic

/-! One genuine physical grade-h field calibration before every perturbative
order, on a prescribed smoothly smeared MS register at the true running
coupling.  The held right-hand physical fields stay exactly unchanged. -/
noncomputable section
namespace YM.Integration.WilsonOrdinaryAllOrderPivot
open Function Matrix Pert Pert.Position MS MS.Local.Physical MS.Menus MS.Land MS.Theater
open FVA2 FVA2.ColorCode Extra.FD OPE.Levy RG11.Fields Pert.RawLabels Pert.Scale
open Extraction Table Spec Climb Filter Set Finset PhysMS MeasureTheory Next.UVStress
open scoped Classical Topology BigOperators ContDiff
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
  (B : Deck G) {O : Booked B} (M : MS_Data G O)
  (F : Spec.Final C f S) (J : ℝ→PhysMS.tower S)
open WilsonMacroscopicRichMeasuredGram WilsonMacroscopicRichRegister
open WilsonOrdinaryPivotAsymptotic
variable (h : ℕ) (g : Test 2) (μ : ℝ)
local notation "Iₕ" => Glyph B h

def rows (k : ℕ) : Iₕ×Iₕ→ℂ := fun z=>MSSeparatedTestGram.matrix M h μ k g z.1 z.2
def curve (t : ℝ) : Matrix Iₕ Iₕ ℂ := fun a b=>realizer (rows B M h g μ) t (a,b)

theorem truncates (q : ℕ) (t : ℝ) (a b : Iₕ) :
    truncation (rows B M h g μ) q t (a,b) = WilsonMacroscopicRichSignedMS.jet B M h g μ q t a b := by
  unfold WilsonMacroscopicRichSignedMS.jet truncation rows
  rw [Finset.sum_apply]
  apply Finset.sum_congr rfl;intro k _
  change (↑(t^k):ℂ)*_=(t:ℂ)^k*_
  rw [Complex.ofReal_pow]

theorem priced (q : ℕ) {γ : ℝ→ℝ} (hγ : Trace.Pilot.Coupling G γ) (hG : G.Simple) :
    ∀ᶠ r in Trace.Pilot.trail,∀ (a b : Iₕ),
      ‖curve B M h g μ (γ r) a b - WilsonMacroscopicRichSignedMS.jet B M h g μ q (γ r) a b‖ ≤
        (‖rows B M h g μ (q+1)‖+2)*(γ r)^(q+1) := by
  have lives : Tendsto γ Trace.Pilot.trail (𝓝[>] (0:ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hγ.conforms hG,hγ.positive⟩
  filter_upwards [lives.eventually (expansion (rows B M h g μ) q)] with r hr
  intro a b
  rw [←truncates]
  exact (norm_le_pi_norm (realizer (rows B M h g μ) (γ r) - truncation (rows B M h g μ) q (γ r)) (a,b)).trans hr

theorem lands {γ : ℝ→ℝ} (hγ : Trace.Pilot.Coupling G γ) (hG : G.Simple) :
    Tendsto (fun r=>curve B M h g μ (γ r)) Trace.Pilot.trail (𝓝 (MSSeparatedTestGram.matrix M h μ 0 g)) := by
  apply tendsto_pi_nhds.mpr;intro a
  apply tendsto_pi_nhds.mpr;intro b
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have bound := (priced B M h g μ 0 hγ hG).mono (fun r H=>H a b)
  have cost : Tendsto (fun r=>(‖rows B M h g μ 1‖+2)*γ r) Trace.Pilot.trail (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x:=‖rows B M h g μ 1‖+2)).mul (hγ.conforms hG)
  apply squeeze_zero' (Eventually.of_forall fun r=>norm_nonneg _) _ cost
  simpa only [WilsonMacroscopicRichSignedMS.jet,Nat.zero_add,Finset.sum_range_one,pow_zero,one_mul,pow_one] using bound

def field {γ : ℝ→ℝ} (r : ℝ) : (Bel C.book).Field h ≃ₗ[ℂ] S.Field h :=
  WilsonOrdinaryPivotFrame.frame B F J h g (fun s=>curve B M h g μ (γ s)) r

/-- The reporting test and this ONE original grade-h field equivalence are
chosen before q. Every signed coefficient removes precisely its prescribed
order; the tariff is uniform over the entire original field register. -/
theorem original (hG : G.Simple) (leading : PhysMS.Leading F J)
    (live : IsUnit (MSSeparatedTestGram.matrix M h μ 0 g)) {γ : ℝ→ℝ} (hγ : Trace.Pilot.Coupling G γ) :
    (∀ v : (Bel C.book).Field h,Tendsto (fun r=>(J r h).symm (field B M F J h g μ (γ:=γ) r v))
        Trace.Pilot.trail (𝓝 v)) ∧
    ∀ q : ℕ,∀ᶠ r in Trace.Pilot.trail,∀ hr : 0<r,∀ v b,
      let c := (WilsonMacroscopicRichFree.basis C B h).equivFun v
      ‖(exterior B J g hr b).charge F h (field B M F J h g μ (γ:=γ) r v) -
        (WilsonMacroscopicRichSignedMS.jet B M h g μ q (γ r)).vecMul c b‖ ≤
        (∑a,‖c a‖)*((‖rows B M h g μ (q+1)‖+2)*(γ r)^(q+1)) := by
  obtain ⟨exact_read,identity⟩ := WilsonOrdinaryPivotFrame.calibrated B M F J h g leading μ live
    (fun r=>curve B M h g μ (γ r)) (lands B M h g μ hγ hG)
  refine ⟨identity,fun q=>?_⟩
  filter_upwards [exact_read,priced B M h g μ q hγ hG] with r read price
  intro hr v b
  let c := (WilsonMacroscopicRichFree.basis C B h).equivFun v
  let A := curve B M h g μ (γ r)
  let P := WilsonMacroscopicRichSignedMS.jet B M h g μ q (γ r)
  let D := (‖rows B M h g μ (q+1)‖+2)*(γ r)^(q+1)
  change ‖(exterior B J g hr b).charge F h _ - P.vecMul c b‖≤(∑a,‖c a‖)*D
  rw [show (exterior B J g hr b).charge F h (field B M F J h g μ (γ:=γ) r v)=A.vecMul c b from read hr v b]
  change ‖(∑i,c i * A i b) - ∑i,c i * P i b‖ ≤ _
  rw [←Finset.sum_sub_distrib,Finset.sum_mul]
  calc
    _ ≤ ∑i,‖c i * A i b - c i * P i b‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum;intro i _
      rw [←mul_sub,norm_mul]
      exact mul_le_mul_of_nonneg_left (price i b) (norm_nonneg _)

end YM.Integration.WilsonOrdinaryAllOrderPivot
end

