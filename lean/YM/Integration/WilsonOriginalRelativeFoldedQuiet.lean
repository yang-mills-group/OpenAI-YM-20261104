import YM.Integration.WilsonOriginalFoldedMarkedIncome
import YM.Integration.WilsonVacuumPreResetDepositedPhase

/-! The measured relative RG02 forest and the covered vacuum have the same positive angular input.
The difference is one coupling scalar before integrating any occupied coefficient. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalRelativeFoldedQuiet
open Function Filter Finset Lattice RG Wilson Precision Tree Exterior FreeResolvent PowerSeries Matrix
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Mer
open scoped Classical BigOperators
variable {G:Gauge}{c f:Side}


private def displacement (P Q:PChart G f) : PowerSeries ℝ :=
  mk fun d => MvPolynomial.eval 0 (coeff d (Blue.flash P-Blue.flash Q))

def correction (b:PowerSeries ℝ) : PowerSeries ℝ := mk fun d =>
  if d=0 then 0 else -coeff d b
def credit (P Q:PChart G f) := correction (displacement P Q)

private def center {D:Type*}[CommRing D](s:PowerSeries D) := s-PowerSeries.C (constantCoeff s)

private theorem retained {A B:Type*}[CommRing A][CommRing B]
    (φ:PowerSeries A →+* PowerSeries B)(hx:φ X=X){k:ℕ}{p q:PowerSeries A}
    (eq:Equal k p q) : Equal k (φ p) (φ q) := by
  have zero : (X:PowerSeries A)^k ∣ p-q := X_pow_dvd_iff.mpr fun j hj =>by rw [map_sub,eq j hj,sub_self]
  obtain ⟨r,hr⟩:=zero
  have image : (X:PowerSeries B)^k ∣ φ p-φ q := by
    rw [←map_sub,hr,map_mul,map_pow,hx]
    exact dvd_mul_right _ _
  intro j hj
  exact sub_eq_zero.mp (by simpa only [map_sub] using X_pow_dvd_iff.mp image j hj)

private theorem terrace {U V:Type}(b:PowerSeries ℝ) :
    holdUp U (soil (U:=V) b)=soil (U:=U⊕V) b := by
  apply PowerSeries.ext
  intro d
  simp [holdUp,holdUpPoly,soil,coeff_map]

private theorem source (S:StepData c f)(F:Forest S.ratio)(M:Matrix (Body 1 f) (Body 1 c) ℝ)
    (P Q:PChart G f){k:ℕ}
    (law:∀t<k,coeff t (Blue.flash P-Blue.flash Q)= MvPolynomial.C (coeff t (displacement P Q))) :
    Equal k (unscaled S F M P-unscaled S F M Q) (soil (displacement P Q)) := by
  intro t ht
  simp only [unscaled,add_sub_add_right_eq_sub,←map_sub,loom,coeff_map,law t ht,soil]
  simp [cord]

open PhysicalNext.Repeat.Legato FreeResolvent
open WilsonVacuumPreResetStationaryChange WilsonVacuumPreResetDepositedRay
open WilsonVacuumPreResetDepositedGeometric WilsonVacuumPreResetDepositedLetters
open WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonVacuumPreResetDatedDeposit (Issued)
open WilsonVacuumPreResetOriginalOutput (covered)
open WilsonCoeffUV.Winding WilsonCoeffUV.Embroider WilsonCoeffUV.Bank Ticket Cosmos Polestar WilsonCoeffUV.Bank.Mosaic
variable (R:Run G)(N i p:ℕ)(hi:i<N)(F:Forest (step R i p).ratio)
local notation "S" => step R i p
local notation "activeKey" => Active G F
local notation "coarseKey" => Woods G (coarse R i p)

def relative (Q:PChart G (fine R i p)) :
    Ink ((Active G F) ⊕ Woods G (coarse R i p)) :=
  let a := relativeHaar R N i p hi F -
    retool (WilsonVacuumPreResetStationaryChange.shift R N i p hi F)
      (unscaled S F (prediction R N i p) Q)
  a - PowerSeries.C (constantCoeff a)

private theorem adjusted {T:Type}(H A B:Ink T)(s:PowerSeries ℝ){k:ℕ}
    (law:Equal k (A-B) (soil s)):
    Equal k (center (H-A)) (center (H-B)+soil (correction s)) :=by
  intro t ht
  have result:=law t ht
  simp only [map_sub,soil,coeff_map] at result
  by_cases zero:t=0
  · subst t
    simp [center,coeff_zero_eq_constantCoeff_apply,soil,correction]
    rw [←coeff_zero_eq_constantCoeff_apply,coeff_map,coeff_mk,if_pos rfl,map_zero]
  · simp only [center,map_add,map_sub,coeff_C,sub_zero,soil,coeff_map,correction,coeff_mk,if_neg zero,map_neg]
    linear_combination -result

include hi in
private theorem filing (e:ℕ)(Z:SeriesA G){σ C:ℝ}(issued:Issued R N (i+1) e Z σ C) :
    let P:=filed R N i p Z
    let Q:=covered R N i p
    ∀ t<3+e, coeff t (Blue.flash P-Blue.flash Q)=MvPolynomial.C (coeff t (displacement P Q)) :=by
  intro P Q
  have kp:(income R N i p).path=R.alloy.B.kin.path N (i+1):=(RunFormalChain.fromRun R).selected N p (i+1) hi
  have kb:(income R N i p).clip=((levels R).params (i+1)).clip:=(RunFormalChain.fromRun R).clips N p (i+1) hi
  have rows (t:ℕ)(ht:t<3+e)(l:ℕ):P t (l+1)=Q t (l+1):=by
    unfold P filed
    rw [kp,kb];exact issued.periodic t ht (fine R i p) l
  have shell:shellK 2 P:=WilsonLimitConstruction.FundedSpringPeriodGerm.grade _ _ _ _
  intro t ht
  rw [displacement,coeff_mk]
  exact WilsonVacuumPreResetFoldedInlet.fieldIndependent P Q t shell (rows t ht)


private theorem shifted (A B:PChart G (fine R i p)){k:ℕ}
    (field:∀t<k, coeff t (Blue.flash A-Blue.flash B)=MvPolynomial.C (coeff t (displacement A B))) :
    let T:=retool (WilsonVacuumPreResetStationaryChange.shift R N i p hi F)
    Equal k (T (unscaled S F (prediction R N i p) A)-T (unscaled S F (prediction R N i p) B))
      (soil (displacement A B)) :=by
  intro T
  have tX:T X=X :=by simp only [T,retool,reroll_X]
  have framed := retained T tX (source S F (prediction R N i p) A B field)
  have invariant : T (soil (U:=(activeKey)⊕(coarseKey)) (displacement A B)) = soil (U:=(activeKey)⊕(coarseKey)) (displacement A B) :=by
    rw [←terrace (U:=activeKey) (V:=coarseKey),retool_tall]
  rwa [map_sub,invariant] at framed

theorem original (e:ℕ)(Z:SeriesA G){σ C:ℝ}(issued:Issued R N (i+1) e Z σ C) :
    let P:=filed R N i p Z
    let Q:=covered R N i p
    Equal (3+e) (opened R N i p hi F Z)
      (relative R N i p hi F Q + holdUp (activeKey) (soil (U:=coarseKey) (credit P Q))) := by
  intro P Q
  rw [terrace]
  exact adjusted _ _ _ _ (shifted R N i p hi F P Q (filing R N i p hi e Z issued))

end YM.Integration.WilsonOriginalRelativeFoldedQuiet
