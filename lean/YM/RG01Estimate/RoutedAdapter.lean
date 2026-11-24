import YM.RG01Estimate.Routed
import YM.RG01Estimate.CensusAtFamily

/-!
# Account from actual purchase & step receipt

Applies also AFTER a representation change has preserved a lawful split at this point (not
assuming it preserves in general); all unknown error is picked off `E`. The high pieces here
are pre-affine projection/real-log prizes. This isn't a theorem permitting an arbitrary new
set of curriculum delays on an existing `C`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Routed
open Function Filter Set Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Control Window Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Shoot Precision SectorMeasure Oriented Reserves
open PhysicalNext PhysicalNext.Repeat Height Beam Brim Match Song
open Next.Scheduling AnalyticBridge VerifiedReset Collection Quotes UVNext Extra.Iteration Meadow
open PriceCompiler Org Input Supply Pressure.Testing Time
open Roost Opera
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Expense Reprice
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} (g:G.Simple) {M : Metals G} {D : Rolls M.p} {A : Alloy M D} (R : Factor A)
    {ε : ℝ}
local notation "T"=> A.B.a

variable {m N n : ℕ} (U : RG.Rep G (A.B.a.S.side (m+1) n))
local notation "p" => A.B.a.budget m
local notation "K" => A.B.a.params m
local notation "χ"=> Chi.canonical
local notation "Φ"=> A.B.kin.alpha N m
structure EquivalentParameters (N : ℕ) (m : ℕ) (n : ℕ) (U : RG.Rep G (A.B.a.S.side (m+1) n)) : Prop where
  paths : U.path = A.B.kin.path N (m+1)
  clip : U.clip= (A.B.a.params (m+1)).clip
  point : U.p= A.B.a.budget (m+1)
  beta : U.beta ∈ Shoot.band T (m+1)
  lawful : U.activities.Valid U.p (A.B.a.clock.allowance (m+1)) (A.B.a.clock.forcedAllowance (m+1))

/-- Any re-expressed lawful vacuum at this step. Variant with optional unnormalized
scalar (cash keeps it). -/
lemma supplies (h : EquivalentParameters (A:=A) N m n U) (hp : m < N) :
    ∃ H :Guide A.B R.shape N m n U, Opera.Price A.B R.shape N m n U H:= by
  let x:= A.B.a.clock.hatBeta m; let P:=A.B.a.clock.op m n; let T':= ships A.B N m n
  let U':=A.B.a.clock.hatBeta (m+1)
  have he : U'=betaF G x P.patch.L:=ConnectedActivityE6.Application.clock_next T m n
  have hy:= Planning.testing A.B R.shape R.pledging.conducts.income.grow.1 N m n hp
  apply (hy.2.2.2.2 _ _ _ _ hy.2.2.1).2 (Opera.protocol A.B hp R.pledging.conducts.full)
  have ht := proceeds A.B N m n hp
  refine ⟨ht,⟨?_,h.clip,?_⟩,⟨?_,?_⟩,?_,?_,?_,?_⟩
  · rw [h.paths]; rfl
  · change _= temp (betaF G x P.patch.L); rw [h.point, ← he]; rfl
  · have hg : A.B.a.clock.loopCap (m+1) ≤ ConnectedActivityE6.loopBill G P.patch.L x := by
      unfold Calendar.loopCap ConnectedActivityE6.loopBill Delay.fineMonitor; rw [← he]
      have he := A.B.a.clock.adm (m+1)
      have ht := A.B.a.fits.thetaRange (m+1)
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [show Vac.Numbers.P U' = (A.B.a.clock.monitor (m+1)) ^ (1:ℝ) by rw [Real.rpow_one]; rfl]
      apply Real.rpow_le_rpow_of_exponent_le (Real.one_le_exp (sq_nonneg _)); refine ht.2.trans (inv_le_one_of_one_le₀ ?_); exact_mod_cast show 1 ≤ A.B.a.clock.J (m+1) by omega
    rw [h.paths,h.clip]; change PathData.Bounds _ _ (M.p.profile _).width (M.p.profile _).paths _
    rw [← params_eq A.B.valid (m+1)]; exact { A.B.support.cap N (m+1) hp with two := budget_loosen (A.B.support.cap N (m+1) hp).two hg }
  · change U.activities.Valid _ (incomingE G P.patch.L x) (incomingK G P.patch.L x)
    unfold incomingE incomingK Delay.fineMonitor; rw [← he]; exact h.lawful
  · rw [h.point]; exact congr_arg RG.Stage.supportExponent (params_eq A.B.valid (m+1)).symm
  · exact he ▸ A.B.a.fits.delayed (m+1)
  · change _=radiusB (betaF G x P.patch.L); rw [← he,h.point]; rfl
  change betaF G x P.patch.L / 2 ≤ U.beta ∧ U.beta ≤ _; exact he ▸ h.beta


include g
lemma ready_debt (r:ℕ) (h : 2≤r) (η c : ℝ) (hv:0<η) (he:η < (1/2:ℝ)) (hc:0<c) :
    ∀ᶠ m:ℕ in atTop, ∀ β∈ Shoot.band T (m+1), c * (Real.sqrt β)⁻¹ ^ ((r:ℝ) + 1 - η) ≤ Fate.debt r G (D.L (A.B.a.clock.J (m+1))) (A.B.a.clock.hatBeta m) := by
  let C:= T; let a (i:ℕ):= C.clock.hatBeta i
  let d:ℝ:= (r:ℝ)+1-η
  have hh : 0<d:=by unfold d; have hp: 2≤(r:ℝ):= (by exact_mod_cast h); linarith
  have hD : -d/2 < Fate.tender r:= by unfold Fate.tender Fate.aim d; push_cast; linarith only [he]
  have hC:Tendsto (fun i=> a (i+1)) atTop atTop:= (WardBin.bell C g).comp (tendsto_atTop_mono (l:=atTop) (f:=id) (fun i:ℕ=>Nat.le_succ _) tendsto_id)
  filter_upwards [((tendsto_rpow_atTop (show 0< Fate.tender r - (-d/2) from sub_pos.mpr hD)).comp hC).eventually_ge_atTop (c*((2:ℝ)^d))]
    with i hi β hβ
  let w:= (Real.sqrt β)⁻¹
  let u:= a (i+1)
  have ht : 0<u:= WardBin.hot C _
  have hg := band_gap (a (i+1)) β ht (trial_in hβ)
  have hp := StepRate.calibration C hβ
  have hz : w ≤ 2 * (Real.sqrt u)⁻¹:= by
    exact hg.2
  have hM: (((Real.sqrt u)⁻¹:ℝ)^d)=u^(-d/2):= by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg ht.le, ← Real.rpow_mul ht.le]; congr 1
    ring
  unfold Fate.debt; rw [← PriceCompiler.beta_eq A.B.valid i]
  apply le_trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hp.2.1.le hz hh.le) hc.le); rw [Real.mul_rpow zero_le_two (inv_nonneg.mpr (Real.sqrt_nonneg _)), hM]
  change c*(_ * u^(-d/2)) ≤ u^Fate.tender r
  rw [← mul_assoc]
  apply le_trans (mul_le_mul_of_nonneg_right hi (Real.rpow_nonneg ht.le _)) (le_of_eq ?_)
  exact (Real.rpow_add ht _ _).symm.trans (congr_arg _ (sub_add_cancel ..))

lemma precision (r:ℕ) (η:ℝ) (hv:0<η) (he:η<1/2) (c:ℝ) (hp:0<c) (hR:2 ≤ r) (h: Allowed R) :
    ∀ᶠ m in atTop, ∀ N n, m<N → ∀ U : RG.Rep G (A.B.a.S.side (m+1) n), EquivalentParameters (A:=A) N m n U →
      ∃ (H : Guide A.B R.shape N m n U) (D' : Alliance H H 1 0), D'.units=Equiv.refl _ ∧ ∀ E τ,
        Inherit.Debits U E τ → τ ≤ c*(Real.sqrt U.beta)⁻¹^((r:ℝ)+1-η) →
        let P:=A.B.a.budget m
        let D₀ := marquee H P
        let γ:= A.B.kin.alpha N m
        let g':= (Real.sqrt U.beta)⁻¹
        Collection.Local D₀ P (Pruned.high H Chi.canonical D' E r γ) (retention R m*τ+spill (A:=A) m r) (CensusStep.hardCost R m) ∧
          spill (A:=A) m r ≤ (A.B.a.clock.hatBeta (m+1))^(-(1/64):ℝ) * (2*g')^(r+1) ∧
          CensusStep.hardCost R m ≤ Real.sqrt (A.B.a.clock.forcedAllowance m)* (2*g')^(r+1) ∧
          ∃ w, Collection.Local D₀ P (Pruned.low H Chi.canonical D' E r γ) w (CensusStep.hardCost R m) ∧
            ∀ O : Tree.Forest (A.B.a.clock.op m n).ratio, ∀ V,
              (A.B.a.clock.op m n).push U.beta U.eval V = earlyValue D₀ (A.B.kin.path N m) (A.B.a.params m).clip P
                (Pruned.low H Chi.canonical D' E r γ) U.beta (Song.weighty H Chi.canonical O) γ V *
                  Real.exp (-(D₀.read (Pruned.high H Chi.canonical D' E r γ)).additive P V) := by
  filter_upwards [ready_debt (A:=A) g r hR η c hv he hp, StepRate.threshold_fine_divisor T g (r+1), (A.B.a.fits.deep.comp (tendsto_atTop_mono (l:=atTop) (f:=id) (fun i:ℕ=>Nat.le_succ _) tendsto_id)).eventually_ge_atTop r] with m hm ht hP N n hN U hU
  obtain ⟨H,hH⟩:= supplies R U hU hN
  let D' := Match.staple (H:=H) (J:=H) rfl rfl rfl
  refine ⟨H,D',rfl,fun E τ hE hx=> ?_⟩
  intro P D₀ γ g'
  have hT:= step R h hN H hH hU.beta hU.point D' rfl E r hR hP hE (hx.trans (hm _ hU.beta))
  obtain ⟨hF,w,hL,hX⟩:=hT
  refine ⟨hF,?_,(CensusStep.hardCost_allowance R m).trans (ht _ hU.beta),w,hL,fun O V=>?_⟩
  · let b := A.B.a.clock.hatBeta (m+1)
    have ht:0<b:= WardBin.hot ..; have hp:0< Real.sqrt b:= Real.sqrt_pos.mpr ht
    have hβ:= StepRate.calibration T hU.beta
    have hv:b^(-Fate.aim r)=((Real.sqrt b)⁻¹)^(r+1):= by
      unfold Fate.aim; rw [Real.sqrt_eq_rpow,← Real.rpow_neg ht.le, ← Real.rpow_mul_natCast ht.le]; ring_nf
    unfold spill; change b^(-Fate.aim r-_)≤_
    rw [sub_eq_add_neg, Real.rpow_add ht, hv,mul_comm]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_pos.mpr hp).le hβ.2.2 _) (Real.rpow_nonneg ht.le _)
  let z:= (A.B.a.clock.op m n).push U.beta U.eval V
  exact ((CensusStep.eharmony R H H D' hN hH O V).symm).trans
    (VacuumListing.reassemble (A.B.a.budget m) hL hF (Pruned.tracks H Chi.canonical D' E r γ) rfl _ _ _ _ V)

end YM.RG01Estimate.Routed
