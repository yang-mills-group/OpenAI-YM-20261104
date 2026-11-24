import YM.AnalyticBridge.GAUSSIAN_FIELD_ALIGNMENT.Services
import YM.Next.FLUCTUATIONS.Grants
import YM.Integration.WilsonLimitConstruction.FundedPredictionSupply
import YM.Integration.RunFormalChain
import YM.Extra.ITERATION_NO_LOSS.Scales

/-! The complete original Gaussian and finite-window tariffs are bought
before the physical calendar. The stagewise caps may grow arbitrarily across
the preselected transitions. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ManuscriptQLocalWindowPurchase
open Function Filter Lattice Wilson RG Tree Precision Pressure Supply Testing Stores
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Org Input Push Push.PriceCompiler Push.SectorMeasure Next.SectorChange Next.SectorChange.Rows
open AnalyticBridge AnalyticBridge.GaussianFieldAlignment
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open scoped Classical Topology
variable {G : Gauge}

/-- The original `till` cuts at a fixed 100000th of the original radius.
Any finite stage tariff multiplying its genuine cut error can be paid before
the stage's inverse coupling, even for a prescribed arbitrary real exponent. -/
theorem tail (r : Rates) (surcharge exponent : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      (1+|surcharge|)*(r.C*(Real.exp (-r.s * (till x : ℝ))*r.D)*r.C) ≤ x^(-exponent) := by
  let a := r.s/200000
  let A := (1+|surcharge|)*r.C*r.D*r.C
  have ha : 0<a := div_pos r.width_pos (by norm_num)
  filter_upwards [Extra.Iteration.Scales.first a (exponent+1) ha,
    Work.E01.radiusB_tendsto.eventually_ge_atTop 200000,
    eventually_ge_atTop A,eventually_gt_atTop (0:ℝ)] with x hx hB hA hxpos
  have hn : radiusB x ≤ 200000*till x := by unfold till; omega
  have hr : (radiusB x : ℝ) ≤ 200000*(till x:ℝ) := by exact_mod_cast hn
  have he : Real.exp (-r.s*(till x:ℝ)) ≤ Real.exp (-a*(radiusB x:ℝ)) := by
    apply Real.exp_le_exp.mpr
    dsimp [a]
    nlinarith [mul_le_mul_of_nonneg_left hr r.width_pos.le]
  have hc : 0 ≤ A := by
    have hC := r.cost_pos
    have hD := r.tail_nn
    dsimp [A]
    positivity
  calc
    _ = A * Real.exp (-r.s*(till x:ℝ)) := by dsimp [A]; ring
    _ ≤ A*x^(-(exponent+1)) := mul_le_mul_of_nonneg_left (he.trans hx) hc
    _ ≤ x*x^(-(exponent+1)) := mul_le_mul_of_nonneg_right hA (Real.rpow_nonneg hxpos.le _)
    _ = x^(-exponent) := by
      calc
        x*x^(-(exponent+1)) = x^(1:ℝ)*x^(-(exponent+1)) := by rw [Real.rpow_one]
        _ = x^(1+(-(exponent+1))) := (Real.rpow_add hxpos ..).symm
        _ = _ := by congr 1; ring

def Paid (weight : ℕ → ℕ → Rates → ℝ) (exponent : ℕ → ℕ → ℝ) : Prediction G :=
  fun {M} {_} {A} _ => ∃ r : Tickets, Earned M.K A.delay r ∧
    ∀ j x, A.delay.betaEntry j≤x → ∀ i, StepStages j i →
      (1+|weight j i (r j i)|)*((r j i).C*(Real.exp (-(r j i).s*(till x:ℝ))*(r j i).D)*(r j i).C) ≤
        x^(-exponent j i)

theorem prepaid (weight : ℕ → ℕ → Rates → ℝ) (exponent : ℕ → ℕ → ℝ)
    (s : Sheet G) (price : MapPrices) : Prepaid (Paid weight exponent) s price := by
  intro _ _ _ _ _ _ _
  obtain ⟨k,hk⟩ := Next.Fluctuations.pressure_pricing s price
  refine ⟨k,fun n hn D _ _ _ _ _ θ _ _ V _ => ?_⟩
  obtain ⟨V₁,hs,hg,he,hb,ν,hν,_⟩ := hk n hn D 0 le_rfl θ V
  have h01 : DelayLe V V₁ := ⟨hb,he.symm.le,hs.symm.le,hg.symm.le⟩
  obtain ⟨V₂,r,_,_,h12,_,hR⟩ := GaussianFieldAlignment.issue_windows V₁ (Next.Foundations.chart_ok G) hν
  let paid j i (x:ℝ) :=
    (1+|weight j i (r j i)|)*((r j i).C*(Real.exp (-(r j i).s*(till x:ℝ))*(r j i).D)*(r j i).C) ≤
      x^(-exponent j i)
  obtain ⟨β,_,hβ,hβ'⟩ := collect_upper V₂.betaEntry (fun j x => ∀ i, StepStages j i → paid j i x)
    (fun j => eventually_transitions j _ _ (fun i _ => tail (r j i) (weight j i (r j i)) (exponent j i)))
  let V₃ : Delays θ := {V₂ with betaEntry := β}
  have h23 : DelayLe V₂ V₃ := ⟨hβ,le_rfl,le_rfl,le_rfl⟩
  refine ⟨V₃,h01.trans (h12.trans h23),fun V₄ h34 _ _ _ _ => ?_⟩
  intros
  exact ⟨r,(hR V₄ (h23.trans h34)).2.2,fun j x hx => hβ' j x ((h34.beta j).trans hx)⟩

theorem allPrices (weight : ℕ → ℕ → Rates → ℝ) (exponent : ℕ → ℕ → ℝ) :
    FundedPredictionSupply.AllPrices (@Paid G weight exponent) :=
  fun s _ => prepaid weight exponent s _

/-- Every actual forest and period at the unfixed interior step, using the
same upper hardware which received the preceding preselection. -/
theorem realized (R : Run G) {weight : ℕ → ℕ → Rates → ℝ} {exponent : ℕ → ℕ → ℝ}
    (paid : Paid weight exponent R.kit) (N m p : ℕ) (hm : m<N) :
    let S := R.alloy.B.a.clock.op m p
    let x := R.alloy.B.a.clock.hatBeta m
    let j := R.alloy.B.a.clock.J (m+1)
    let i := R.alloy.B.a.clock.J m
    let T := ships R.alloy.B N m p
    ∃ r : Rates,
      (∀ (A : Stores S) (F : Forest S.ratio) (k : S.Choices) (V : Config G _),
        A.flags=RG.flags (temp x) V ∨ V=1 → Ready A F x T k V r.s r.η r.C r.D) ∧
      (1+|weight j i r|)*(r.C*(Real.exp (-r.s*(till x:ℝ))*r.D)*r.C) ≤ x^(-exponent j i) := by
  intro S x j i T
  obtain ⟨r,ready,budget⟩ := paid
  let B := R.alloy.B
  have step := step_paid B.a m
  have first := first_le B.valid m
  have use := ready j i step first x (B.valid.pays m)
  have hl : S.patch.L=R.rolls.L j := block_eq B.valid m
  have hs : 100*(1+radiusB x)≤(B.a.S.side m p).val := by
    rw [add_comm 1]; exact B.a.fits.sizeT m p
  exact ⟨r j i,use _ _ S rfl hl (Next.SectorChange.Client.funded B R.kit.machine.ring R.kit.machine.bill N m p hm)
    hs T (Pressure.Testing.proceeds B N m p hm),budget j x (B.valid.pays m) i step⟩

end YM.Integration.ManuscriptQLocalWindowPurchase
end
