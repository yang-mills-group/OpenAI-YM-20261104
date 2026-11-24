import YM.Integration.WilsonMeasuredPublicEntranceTrialPeerBoard
import YM.Integration.WilsonSeparatedPrefixCanonicalMounted
import YM.Integration.WilsonThermometerSameWalkSectionFare

/-! The paid exponent for cropping physical peers on the trial gallery. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceCropLedger
open Filter Finset Lattice Wilson RG Labels Source Marker QuadraticLocal
open PhysicalNext PhysicalNext.Repeat Legato Extra.Histories
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){V:Type}[Fintype V][DecidableEq V](d:V→ℕ)
local notation "C" => R.family
local notation "A" => (C).path.levels

theorem original (simple:G.Simple)(pace:WilsonWindowReportingPace.Slow R.kit)
    (book:WilsonReportLampForecast.Ready (A)):
    ∀ᶠ f:ℕ in atTop,∀N p (_:f≤N),∀(W:Rep G ((C).side f p)),
    W.p=(A).budget f → ((A).params f).supportExponent=100 →
    ∀(o:V→Site ((C).side f p))(q:∀v,Coefficient ((C).labels.level (d v)) ((C).side f p))
      (B w:V→ℝ)(D t:ℕ)(trial:Finset V),
    let H:=(A).clock.hatBeta f
    (∀v,0≤B v) → (∀v,0≤w v ∧ w v≤1) →
    (∀v,WilsonSeparatedPrefixCanonicalMounted.salary R d f p q B v≤H^t) →
    WilsonMeasuredPublicEntranceTrialPeerBoard.price (N:=N) R d o W q trial w (fun _=>D) B 1 ≤
      (Fintype.card V:ℝ)*Real.exp (3*(D:ℝ))*H^t:=by
  have stock:∀ᶠ f:ℕ in atTop,∀v:V,∀N p:ℕ,f≤N → ((A).params f).supportExponent=100 →
      ∀{U:Type} (o:U→Site ((C).side f p)) (j:U) (y:(C).label (d v)) (w:U→ℝ),0≤w j →
      WilsonOriginalStarPrimaryCatalog.rent R N p f (d v) o j y w (100+1+1) ≤
        ((A).clock.hatBeta f)^6*(w j*((C).labels.level (d v)).coeffSize y):=
    Filter.eventually_all.mpr (fun v=>WilsonThermometerSameWalkSectionFare.original R (d v) simple pace book)
  filter_upwards [stock,WilsonThermometerSameWalkWindow.original R simple book] with f first edge
  intro N p cut W point sr o q B w D t trial H bn widths bills
  have one:1≤H:=((A).fits.delayed f).le
  have h:0≤H:=zero_le_one.trans one
  have exp:1≤Real.exp (3*(D:ℝ)):=Real.one_le_exp (by positivity)
  have inside:W.p.supportExponent=100:=by rw [point];exact sr
  have base:WilsonRetainedMarkedInletRegular.cost W.p≤H^2:=by
    simpa [H,WilsonThermometerSameWalkWindow.length] using (edge p W point 0).1
  unfold WilsonMeasuredPublicEntranceTrialPeerBoard.price
  calc
    _ ≤ ∑_v:V,Real.exp (3*(D:ℝ))*H^t:=by
      apply Finset.sum_le_sum
      intro v _
      split_ifs
      · exact one_le_mul_of_one_le_of_one_le exp (one_le_pow₀ one)
      · have wages:=first v N p cut sr o v (q v).x w (widths v).1
        have x:0≤((C).labels.level (d v)).coeffSize (q v).x:=Finset.sum_nonneg fun _ _=>norm_nonneg _
        have upper:w v*((C).labels.level (d v)).coeffSize (q v).x≤((C).labels.level (d v)).coeffSize (q v).x:=
          mul_le_of_le_one_left x (widths v).2
        have paid:=wages.trans (mul_le_mul_of_nonneg_left upper (pow_nonneg h _))
        rw [show (100+1+1:ℝ)=100+2 by norm_num] at paid
        have hard:=mul_le_mul base (mul_le_of_le_one_left (bn v) (widths v).2)
          (mul_nonneg (widths v).1 (bn v)) (pow_nonneg h _)
        have soft:=le_mul_of_one_le_left (mul_nonneg (pow_nonneg h 6) x) exp
        unfold WilsonMeasuredPublicEntranceCropFamily.fare
        rw [inside]
        change _+Real.exp (3*(D:ℝ))*_ * _ ≤ _
        rw [mul_assoc]
        apply (add_le_add (paid.trans soft) (mul_le_mul_of_nonneg_left hard (Real.exp_pos _).le)).trans
        rw [←mul_add]
        exact mul_le_mul_of_nonneg_left (bills v) (Real.exp_pos _).le
    _ = _:=by simp;ring

end YM.Integration.WilsonMeasuredPublicEntranceCropLedger
end
