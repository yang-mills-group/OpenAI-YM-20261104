import YM.QuadraticLocal.Perspective.Locator
import YM.QuadraticLocal.Class.Divisor
/-!
 # Quantitative post-movement actual Mark step invoices

 adapt `PaceR.bill_compact` and `Qarry` to the general-E case: Here not using
 Path.Track old x, only branch β availability (true condition for arbitrary input).
 Marker-load enhancement (post-block worksheet) pays only at the genuine polynomial
 demand assembled ahead. Even if rough wave uses many markers, still pays the full
 general Wall pay-log. No claim of exponential smallness of output after division
 on a high number of markers.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Advent
open Function Filter Finset Lattice Wilson RG RG.Supply Pressure Input Org Precision Next.Scheduling
open Next.Scheduling.Clock AnalyticBridge VerifiedReset ConnectedActivityE6 PhysicalNext Repeat
open Progress.DirectedRecipe Payments Push AbsoluteSums PriceCompiler
open AllOrder AllOrder.Transit WheelP AllOrder.Floe AllOrder.Floe.Step PlanV Pane ThroughLaunch
open Roost Legato Graces
open Extra.Iteration
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius Asymptotics
open Extra.Histories
variable {G: Gauge} (R:Run G) (g : G.Simple)
local notation "S"=> R.alloy.B.a
local notation "Ta"=> R.T
local notation "Sz"=> R.metals.p
local notation "A"=> R.alloy
local notation "F"=> R.kit
local notation "Z"=> R.family
local notation "c"=> R.family.side
variable {m n i b q k N:ℕ} (h:WayStation R.kit) (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
variable (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)(Q:D.Tab R.rolls)
set_option quotPrecheck false
local notation "ρ"=> Burn.horizon k
local notation "Φ"=> R.alloy.B.a.clock.hatBeta
local notation "τ"=> R.alloy.B.a.clock.op i n
local notation "Y"=> R.alloy.B.a.clock.J (i+1)
local notation "I"=> R.alloy.B.a.clock.J i
local notation "L"=> R.rolls.L Y
local notation "X"=> R.alloy.B.a.budget i
local notation "W"=> R.alloy.B.a.budget (i+1)
local notation "xd"=> Φ i
local notation "γ"=> Φ (i+1)
local notation "Vd"=> (Φ i)
variable (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin)(Ψ:(i:ℕ)→RG.Rep G (R.family.side i n))
variable (v:Concourse R.alloy R.kit R.T π Γ m N n k Ψ)
variable (K₀:TicketP R.alloy R.kit D Q)
variable (l:m≤ i)
local notation "P"=> Ψ (i+1)
local notation "P'"=> Ψ i
local notation "H"=> Opera.Guide R.alloy.B (R.kit.shape)
local notation "wa"=> Time.forecastK S i (R.kit).scout (P).beta
local notation "wp"=> Time.quoteHard S i (R.kit).book (P).beta
local notation "y₀"=> Willow.haloSlack (X).B
local notation "Γ'"=> R.T.history N n
open Integration.LocalComparison
open Marker
namespace Sycamore
-- eventually pay EVERY polynomial cost of restoring
set_option quotPrecheck false
local notation "Φd"=> Φ b
local notation "δ"=> forcedDivisor Z i
local notation "Op'"=> R.family.path.levels.clock.op i n -- weird
namespace Quark
-- Wall.Coupe. Local threshold.Pl.G. Pay powers using any stage raw Quote.Lessen factor outside, preserving exponential WP^1/2

open Coat PaceR
variable {β:ℝ} (hvb:β∈ RG.Shoot.band R.alloy.B.a (i+1))
local notation "t"=> (Φ (i+1))
local notation "V_"=> ( Coat.gStep β )
include g
lemma rise : Tendsto (fun i:ℕ=> Φ (i+1)) atTop atTop:= (Sycamore.too R g).comp (tendsto_atTop_mono (f:=id) (g:=fun x:ℕ=>x+1) (fun k=>Nat.le_succ k) tendsto_id)
omit g
lemma thin : Tendsto (fun i:ℕ=> Mentor.Tolerance ( R.alloy.B.a.clock.J i )) atTop (𝓝 (0:ℝ)):= by
  let f i:=(S).clock.J i+1
  have h:Tendsto f atTop atTop:= tendsto_atTop_mono (fun k=> Nat.le_succ ((S).clock.J k)) (S).fits.deep -- α includes macro binder fails inside type. adjust
  simp only [Mentor.Tolerance,one_div]; exact tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp h)
lemma gram (i:ℕ): Mentor.Tolerance i= Beaming.grain i:=by unfold Mentor.Tolerance Beaming.grain;push_cast;rfl
include h hvb
lemma force_cost {u:ℕ}(ht:u ≤ R.alloy.B.a.clock.J i) : quoteR R β i ≤ (t)^(-(u:ℝ))*forcedDivisor Z i :=by
    have hh':= h.frost.bears _ _ _ (step_paid S i) (R.alloy.B.valid.pays i); have ha:=PriceCompiler.beta_eq R.alloy.B.valid i
    have hez:= trial_in hvb; unfold quoteR Time.quoteHard; rw [ha]; exact Beaming.Leg.pretty hh' u ht β (ha ▸ hez)
lemma jet_compact {u:ℕ}
    (hu:u+4≤ R.alloy.B.a.clock.J i)(hx:Φ b/2 ≤ Φ (i+1))(hγ : 2^(u+4) ≤ Φ b) {X' : ℝ}(hS:0≤X') (hβ:X'≤ Φ b) : X' * quoteR R β i ≤ min ((Φ b)^(-(u:ℝ))*δ) (Real.sqrt (quoteR R β i)):=by
    let f:=quoteR R β i; have hp:0< f:=Real.exp_pos _; have hphi:0< Φ b:= positive R b
    let z:=Φ b; have hz:=((S).fits.delayed b).le; have hW:= Quark.force_cost R h hvb hu; have ht := Real.rpow_le_rpow_of_nonpos (half_pos hphi) hx (show -(↑(u+4:ℕ):ℝ) ≤ 0 from neg_nonpos.mpr (Nat.cast_nonneg _)); let ν:= Φ b; let hΩ := ((glyphBound (S) i).1); have hD : δ≤1:= (glyphBound (S) i).2; have h0:0<δ:= hΩ
    have hd : f* z^(u+3) ≤ δ:= by
       let A':=ν
       have hF := mul_le_mul_of_nonneg_right ht h0.le; have hQ := hW.trans hF; rw [Real.rpow_neg (half_pos hphi).le, Real.rpow_natCast,div_pow, ← one_div, div_div_eq_mul_div,one_mul] at hQ; -- rearr
       have hh : f ≤ (δ /(z ^ (u+3))) := by
          change (f) ≤ _; refine hQ.trans ?_; rw [div_mul_eq_mul_div, div_le_div_iff₀ (pow_pos hphi (u+4)) (pow_pos hphi (u+3)),pow_succ (Φ b) (u+3)]; change 2^(u+4)*δ*z^(u+3)≤ δ*(z^(u+3)*z); nlinarith only [mul_le_mul_of_nonneg_right hγ (show 0≤ δ*z^(u+3) from mul_nonneg h0.le (pow_nonneg hphi.le _))]
       exact (le_div_iff₀ (pow_pos hphi _)).mp hh
    apply le_min
    · rw [Real.rpow_neg hphi.le,Real.rpow_natCast, mul_comm _ (forcedDivisor ..),← div_eq_mul_inv]; refine (le_div_iff₀ (pow_pos hphi _)).2 (le_trans ?_ hd)
      have he : X'*(z^u) ≤ z^(u+3):= (mul_le_mul_of_nonneg_right hβ (pow_nonneg hphi.le u)).trans ((show (z*z^u) ≤ z^(u+3) from (by rw [← pow_succ']; exact pow_le_pow_right₀ hz (by omega)))) -- bracket error
      change X'*f*z^u≤ f*z^(u+3); linarith only [mul_le_mul_of_nonneg_left he hp.le]
    · have he : X'^2 * f ≤1:= calc
         X'^2*f ≤ z^2*f:= mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hS hβ _) hp.le
         _ ≤ f * z^(u+3):= by rw [mul_comm (z^2)]; exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hz (by omega)) hp.le
         _ ≤1 := hd.trans hD
      change X'*f ≤ _; apply Real.le_sqrt_of_sq_le; exact (show _≤ _ from by rw [mul_pow,pow_two f,← mul_assoc]; exact mul_le_of_le_one_left hp.le he)

omit h hvb
local notation "T_"=> ( Mentor.Tolerance I )
local notation "Ko"=> (budgetR R i)
variable (jJ r s:ℕ)(ε:ℝ)
noncomputable abbrev fidelity (i j:ℕ)(R:Run G) := ( R.alloy.B.a.clock.hatBeta (i+1) )^( Mentor.Tuition.need j ( Mentor.Tolerance (R.alloy.B.a.clock.J i)))
local notation "q0"=> Quark.fidelity i jJ R
include g
-- every fixed power cost of the actual-K (not just Γ attenuation). drives off arbitrary copy counts only in rough absolute.S.Scope.Height.Frame.*
lemma week (k:ℕ)(ε:ℝ)(hε:0<ε): ∀ᶠ i:ℕ in atTop, (budgetR R i)^k ≤ (Φ (i+1))^ε:= by
    have he : Tendsto (fun i:ℕ=> Beaming.grain ( R.alloy.B.a.clock.J i )*(k:ℝ)) atTop (𝓝 0):= by
       simp_rw [← gram]; simpa only [zero_mul] using (thin R).mul_const (k:ℝ) -- binder `g` not included. `gram` R?
    filter_upwards [he.eventually_le_const hε] with i hi; let x:=Φ (i+1); let Q:= R.alloy.B.a.clock.J i; have hx:1 ≤ x:=(S).fits.delayed _|>.le; have hp:0≤ x:= zero_le_one.trans hx
    calc _ ≤ (x^Beaming.grain Q)^k:=pow_le_pow_left₀ (zero_le_one.trans (budget_pos R)) (min_le_right ..) _
         _ = _ := (Real.rpow_mul_natCast hp (Beaming.grain Q) k).symm
         _ ≤ _:= Real.rpow_le_rpow_of_exponent_le hx hi
omit g
-- maybe `Vℓ.Info.Litness.Binding.Scope.B.Entity` `hβ'` given.betaF.Path true.` power reissue all por.
include hvb
lemma rocket : t ^ (-(s:ℝ)) ≤ ( 2*gStep β )^(2*s):=by
    have ht:= ((S).fits.delayed (i+1)); let x:= t; have hp:0<x:= zero_lt_one.trans ht
    let z:= gStep x; have hz:= Fare.gS x hp|>.1; have he : z/2 ≤ gStep β:= ( band_gap _ β hp (trial_in hvb) ).1
    refine le_trans ?_ (pow_le_pow_left₀ hz.le (show z≤2*gStep β from by linarith only [he]) (2*s))
    rw [Burn.inv_sqrt x hp,← Real.rpow_mul_natCast hp.le]; apply le_of_eq; apply congr_arg (fun p:ℝ=>x^p); push_cast; ring
-- syntax x/z rewriting letx adjust
variable (he:0<ε)(hε:ε≤1/4)
omit hvb
structure Stature (i:ℕ):Prop where
   heightBudget : s+4 ≤ R.alloy.B.a.clock.J i
   forcing : 2^(s+4) ≤ Φ (i+1)
   tenure : Mentor.Tolerance ( R.alloy.B.a.clock.J i ) ≤ ε/4
   wager : (budgetR R i)^(r+1) ≤ (Φ (i+1))^(ε/4)
   bonus : (budgetR R i)^(6*r) ≤ Φ (i+1)
   mint : 4 ≤ Φ (i+1)
include g he
lemma honored : ∀ᶠ i:ℕ in atTop, Stature R r s ε i := by
  have hv:= (rise R g); filter_upwards [ ( R.alloy.B.a.fits.deep ).eventually_ge_atTop (s+4), hv.eventually_ge_atTop (2^(s+4):ℝ), (thin R).eventually_le_const (div_pos he (by norm_num : (0:ℝ)<4)), Quark.week R g (r+1) (ε/4) (div_pos he (by norm_num)), Quark.week R g (6*r) 1 zero_lt_one, hv.eventually_ge_atTop 4 ] with i h₀ h₁ h₂ h₃ h₄ h₅; exact ⟨h₀,h₁,h₂,h₃, h₄.trans_eq (Real.rpow_one _),h₅ ⟩
omit g he
section gate
variable (u:Quark.Stature R r s ε i){Ω:ℝ}(hΩ:1 ≤ Ω)(hK:Ω ≤ budgetR R i)
namespace Stature
include hvb h u
local notation "wp'"=> quoteR R β i
local notation "ϖ"=> ( R.alloy.B.a.clock.forcedAllowance i )
local notation "Ξ"=> (Ω^6)^r*wp'
local notation "V₀"=> ( 2*gStep β )
set_option maxHeartbeats 660000
lemma consuming : 0<gStep β ∧ gStep β ≤1:= by
 let x:=t; have ht:4 ≤ x:=u.mint; have hp:1≤ β:= by linarith only [ (show x/2 ≤ β from hvb.1), ht ]
 unfold gStep; refine ⟨inv_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans_le hp)),inv_le_one_of_one_le₀ ?_⟩; exact le_trans (le_of_eq Real.sqrt_one.symm) (Real.sqrt_le_sqrt hp)
lemma lean : Real.sqrt (quoteR R β i) ≤ R.alloy.B.a.clock.forcedAllowance i:= (Real.sqrt_le_sqrt (Consequence.calmPrice R.kit hvb)).trans_eq (Real.sqrt_sq (Real.exp_pos _).le)
include hΩ hK
lemma shutter : Ξ ≤ Real.sqrt (quoteR R β i)∧ Ξ ≤ ( 2*gStep β )^(2*s) * ( forcedDivisor R.family i ) ∧ Ξ ≤ (ϖ):=by
 let hPH:= ( S ).fits.delayed (i+1); have hΩ:0≤Ω:= zero_le_one.trans hΩ; rw [← pow_mul ]; -- all occurrences? single rw rewrites all? check
 have hu:= (Quark.jet_compact R h hvb u.heightBudget ( div_le_self (show 0≤ t from zero_le_one.trans hPH.le) (by norm_num: (1:ℝ) ≤ 2)) u.forcing (pow_nonneg hΩ (6*r)) ((pow_le_pow_left₀ hΩ hK (6*r)).trans u.bonus )); obtain ⟨hv,h₀⟩:= le_min_iff.mp hu
 refine ⟨h₀,hv.trans (mul_le_mul_of_nonneg_right (Quark.rocket R hvb s) (glyphBound (S) i).1.le),h₀.trans (lean R h hvb r s ε u) ⟩
local notation "λ₁"=> ((jJ:ℝ)+1-ε)
local notation "θc"=> ( (2:ℝ)^ λ₁ * (gStep β )^ λ₁ )
local notation "ϕ"=> ( (Quark.fidelity i jJ R) )
omit h hvb hΩ hK
include hε
lemma funds : 0<Quark.fidelity i jJ R ∧ Quark.fidelity i jJ R ≤ 1:= by
 have he:= ((S).fits.delayed (i+1)); let x:= Mentor.Tolerance I; have hz : Mentor.Tuition.need jJ x ≤ 0:= by unfold Mentor.Tuition.need Catch.graded; let y:=ε; have h0 : x ≤ ε/4:= u.tenure; push_cast; linarith only [hε,h0, Nat.cast_nonneg (α:=ℝ) jJ] -- `α` works? local notation `F`.Z.
 unfold Quark.fidelity; exact ⟨Real.rpow_pos_of_pos (zero_lt_one.trans he) _,Real.rpow_le_one_of_one_le_of_nonpos he.le hz⟩
include hvb hΩ hK
lemma admits : Ω^(r+1)*(ϕ) ≤ θc:=by
 let U:= (jJ:ℝ)+1-ε; have hu:0≤U:= by unfold U; linarith only [hε,Nat.cast_nonneg (α:=ℝ) jJ]
 let x:=t; have hx:1<x:= (S).fits.delayed (i+1); have hp:0<x:= zero_lt_one.trans hx
 let z:= gStep x; have hv:z/2 ≤ V_ :=(band_gap _ β hp (trial_in hvb)).1; have hz:0<z:= (Fare.gS x hp).1; have ht:0<β:=by linarith only [hp, (show x/2≤ β from hvb.1)]
 have he: Ω^(r+1) ≤ x^(ε/4):=( pow_le_pow_left₀ (zero_le_one.trans hΩ) hK (r+1)).trans u.wager; let T':= T_; let Q':= Mentor.Tuition.need jJ (T'); have hQ': ε/4+Q' ≤ -(1/2:ℝ)*U:= by unfold Q' Mentor.Tuition.need Catch.graded U; have h0:T'≤ ε/4:= u.tenure; push_cast; linarith only [h0]
 have he' : x^(ε/4)*ϕ ≤ z^U:= by
    change x^(ε/4) * x^( Mentor.Tuition.need jJ ( Mentor.Tolerance I ) ) ≤ gStep x ^ U; rw [← Real.rpow_add hp, Burn.inv_sqrt _ hp, ← Real.rpow_mul hp.le]; exact Real.rpow_le_rpow_of_exponent_le hx.le hQ'
 apply le_trans (mul_le_mul_of_nonneg_right he (Real.rpow_nonneg hp.le _))
 apply he'.trans; rw [← Real.mul_rpow zero_le_two (Fare.gS β ht).1.le]; exact Real.rpow_le_rpow hz.le (show z ≤ 2*gStep β from (by linarith only[hv])) hu
end Stature
end gate
end Quark
end Sycamore
end YM.QuadraticLocal.Advent
