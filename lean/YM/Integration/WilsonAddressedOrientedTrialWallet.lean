import YM.Integration.WilsonAddressedFiniteThermalWallet
import YM.Integration.WilsonReflectedMixedMasterAxes
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 700000
noncomputable section
namespace YM.Integration.WilsonAddressedOrientedTrialWallet
open Finset Lattice Wilson RG Source Labels Marker QuadraticLocal.Affinity MergeProof.Accent Pert.Asymptotics
open PhysicalNext.Repeat.Legato RegulatorIR Extra.Histories.Motion Push.Local Extra.Histories.Relay
open WilsonReflectedFundedHearing (Arm)
open WilsonReflectedMixedMasterAxes (Fixed)
open WilsonReflectedPublicGuardedMotion (coords)
open WilsonAddressedFiniteThermalInput (vector)
open WilsonAddressedFiniteGuardTrial (printed)
open WilsonAddressedFiniteThermalWallet (mass)
open WilsonOriginalPublicTrialFigure (weight amount measured)
open WilsonOriginalMicroscopicEntranceOpticalUnits (rank)
open WilsonMeasuredPublicEntranceGridDebit (fitted)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){V:Type}[Fintype V][DecidableEq V](d:V → ℕ){N per f K:ℕ}
  (live:K ≤ N)(A:∀v,Arm R (d v) N per f K)(c:V → ℝ)
  (x:Wallet (WilsonOriginalAlternativeFiniteSource.disks (V:=V)))(s:(Stock.census V).Mode)
local notation "H" => R.family.path.levels.clock.hatBeta K
local notation "F" i:max => R.family.labels.level (d i)

def factor (i:V):ℂ:=(c i:ℂ)*(((R.family.S.a K:ℂ)^(d i))⁻¹)

include live in
theorem purchased (power:ℕ)(bank:V → ℝ)(pos:∀v,0 ≤ bank v)
    (earned:∀v,(F v).coeffSize ((((R.family.S.a K:ℂ)^(d v))⁻¹) • (A v).w) ≤ bank v*H^power)
    (cp:∀v,0 ≤ c v)(small:∀v,c v ≤ 1)
    (gReport roof:ℝ)(paid:H*gReport^2 ≤ roof)(places:V → Cover):
    let grades:=fun a:↥s.val=>d a.val
    let g:=regulatorRun R.family N per K
    let v:=fun a=>coords R (A a)
    let z:=factor R d (K:=K) c
    let rows:=vector R d N per K v z x s
    let due:=fun a=>orbitCost (F a)*bank a
    let e:=fun a=>rank R (d a)+power
    (∀U,printed R d (N:=N) (wrap (R.family.side K per) ∘ places) v z x s U=
      measured R grades g rows (fun a=>places a.val) U) ∧
    (∑b,‖weight R grades g rows b‖)*(∏a∈s.val,(gReport^2)^(e a)) ≤ ∏a∈s.val,due a*roof^(e a):=by
  classical
  intro grades g v z rows due e
  have hpos:0 ≤ H:=zero_le_one.trans (R.family.path.levels.fits.delayed K).le
  have own (a:V):(F a).coeffSize (z a • v a) ≤ due a*H^power:=by
    simpa only [v,z,factor,due,mul_assoc] using WilsonReflectedMixedSignedCampus.rotated R (A a) (c a) (cp a) (small a) (earned a)
  have funding:(∑b,‖weight R grades g rows b‖) ≤ ∏a∈s.val,due a*H^(e a):=by
    simp only [WilsonOriginalPublicTrialFigure.weight,norm_prod]
    rw [←Fintype.prod_sum (fun (i:↥s.val)(b:(F i.val).Index)=>‖amount R grades g rows i b‖),
      ←Finset.prod_coe_sort s.val (fun a=>due a*H^(e a))]
    apply Finset.prod_le_prod (fun i _=>Finset.sum_nonneg fun _ _=>norm_nonneg _)
    intro i _
    refine (mass R d N per K live v z x s i).trans ?_
    calc
      _ ≤ H^(rank R (d i.val))*(due i.val*H^power):=mul_le_mul_of_nonneg_left (own _) (pow_nonneg hpos _)
      _ = _:=by rw [show e i.val=rank R (d i.val)+power from rfl,pow_add];ring
  refine ⟨fun U=>WilsonAddressedFiniteThermalInput.original R d N per K _ v z x s places (fun _=>rfl) U,?_⟩
  have cash(a:V):0 ≤ due a:=mul_nonneg (zero_le_one.trans (orbitCost_one_le _)) (pos a)
  calc
    _ ≤ (∏a∈s.val,due a*H^(e a))*(∏a∈s.val,(gReport^2)^(e a)):=mul_le_mul_of_nonneg_right funding
      (Finset.prod_nonneg fun _ _=>pow_nonneg (sq_nonneg _) _)
    _ = ∏a∈s.val,due a*(H*gReport^2)^(e a):=by
      rw [←Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro a _
      rw [mul_pow,mul_assoc]
    _ ≤ _:=Finset.prod_le_prod (fun a _=>mul_nonneg (cash a) (pow_nonneg (mul_nonneg hpos (sq_nonneg _)) _))
      (fun a _=>mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg hpos (sq_nonneg _)) paid _) (cash a))

omit [Fintype V] [DecidableEq V] in
theorem billed (base history:V → ℕ)(target power:ℕ)(first:∀v,base v ≤ f)(up:f ≤ K)
    (Y:∀v,R.family.label (d v))(M bank:V → ℝ)
    (fit:(v:V) → R.family.label (d v) ≃ₗ[ℂ] R.family.label (d v))
    (bought:∀v,Fixed R (d v) (base v) target N per f K (history v) (first v) up live (Y v) (M v)
      (bank v*H^power) (fit v))
    (same:∀v,(A v).w=(fit v).symm (fitted R (d v) (base v) N per (Y v))):
    ∀v,(F v).coeffSize ((((R.family.S.a K:ℂ)^(d v))⁻¹) • (A v).w) ≤ bank v*H^power:=by
  intro v
  rw [same]
  exact (bought v).2.1

end YM.Integration.WilsonAddressedOrientedTrialWallet
end
