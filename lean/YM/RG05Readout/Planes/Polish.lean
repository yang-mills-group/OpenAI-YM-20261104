import YM.RG05Readout.Planes.Trace
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Planes
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories Cells Overlay
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper Motion
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station Ribbons
open Records Basket Halls Shadow Flatten
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {i n m p N d:ℕ}
    {b k l:ℕ}{Q:ℝ}(h:C.Makes){D: Address.Rail C}{B:ℕ→ℕ→ℝ}
set_option quotPrecheck false
open Pulse Extraction Extraction.Lease
open Push.RelayDifference
variable {D:Address.Rail C}

variable {f: Extraction.Order}

/-! A transcription at common origin: affordable → vetted literal against calibrated matrices, absorb a finite bank then same at ALL higher SBP orders on-demand. For low-weight planes repaint them further. -/
open Bay Chalice

/-!
# Cone receipts.Boolean Ward.
 Weighted REAL ancestry maps. Projection kernel not discarded here. This proves linear inverse attenuation for surviving low-engineering weights and propagation bound for the rest, not lower/separated aperture budget by assumption. Using m≫ as required from Husk.C. -/
local notation "Z!"=> C.path.levels
local notation "χ"=> Address.clear C
local notation "S"=> Palette C d
local notation "J"=> Mark C d
local notation "ξ"=> C.S.block
local notation "L"=> C.S.block i
local notation "p!"=> BudgetPoint
variable {e:ℕ}{s t α A E:ℝ}
local notation "ΠΩ"=> Address.clear C d e
local notation "T"=> LinearMap.id (R:=ℂ) (M:=S) - Address.clear C d e
local notation "Ω"=> amplify d C L
/-!
# Toll for strings with these footprints
 All spatial subpowers.Price licenses come before continuing to coupling geometry. -/
variable {H:Sight C d p}{U:Emblems C d}(hw:Awake D B b d)(ht:Spine D B h b p d N H U)
local notation "F'"=> powerFare B d
local notation "P!"=> bounty B d
local notation "H!"=> productCost B d
local notation "Z"=> C.S.block
local notation "S'"=> C.S.scale
local notation "T!"=> ld C.path.levels
open Filter Set OPE
include hw
lemma base_tariff (i:ℕ)(hx:b ≤ i): H! i ≤ 3000 * T! i^4:=by
     obtain ⟨-,hp,-,ht⟩:= always hw i hx; let a:= F' i; have hm:0 ≤ a:=zero_le_one.trans (grows _).1; let b:=T! i
     calc _ = a*(1+4*a^2):=rfl
          _ ≤ (4*b)*(1+4*((4*b)^2)):=by gcongr
          _ ≤ _ := by change _ ≤ 3000*b^4; have he:2≤ b:=ht; nlinarith only [he, show b≤b^4 by simpa only [pow_one] using pow_le_pow_right₀ (by linarith only [he]:1 ≤ b) (by decide:1 ≤4), pow_le_pow_right₀ (by linarith only [he]:1 ≤ b) (by decide:3≤4)]
lemma tariff_power (u:ℝ)(he:0<u) : ∀ᶠ i:ℕ in atTop,productCost B d i≤ ((Z i).val:ℝ)^u:=by
    let x(a):=(↑((Z a).val):ℝ); let ε:=u/8; have hε:0<ε:=by unfold ε; positivity
    filter_upwards [(tendsto_rpow_atTop (half_pos he)|>.comp (lane_rises hw)).eventually_ge_atTop 3000,fur_gain (C:=C) ε hε,eventually_ge_atTop b] with i hi hk hp
    let t:=x i; have hx:0<t:=by unfold t x; positivity
    refine (base_tariff hw _ hp).trans ((mul_le_mul hi (pow_le_pow_left₀ (zero_le_one.trans (lamp_nn (C:=C) i)) hk 4) (pow_nonneg (zero_le_one.trans (lamp_nn _)) _) (Real.rpow_nonneg hx.le (u/2))).trans_eq ?_)
    change t^(u/2)*(t^ε)^4= t^u; rw [← Real.rpow_natCast, ←Real.rpow_mul hx.le,← Real.rpow_add hx]; norm_num only [ε]; congr 1;ring
lemma tariff (η:ℝ)(hp:0<η): ∀ᶠ n:ℕ in atTop, ∀ m:ℕ,n ≤ m→ P! m ≤ P! n * Real.exp (η*(S' m-S' n)):=by
    obtain ⟨v,hv⟩:= eventually_atTop.mp (tariff_power hw η hp); filter_upwards [eventually_ge_atTop v] with n hn m hm
    induction m,hm using Nat.le_induction with
    | base=> rw [sub_self,mul_zero,Real.exp_zero,mul_one]
    | succ i hi ih=>
       rw [bounty_up]; apply (mul_le_mul ih (hv i (hn.trans hi)) (zero_le_one.trans (grows _).2.2.2) (mul_nonneg (zero_le_one.trans (bounty_head _)) (Real.exp_nonneg _))).trans_eq
       rw [Real.rpow_def_of_pos (by positivity),mul_assoc,← Real.exp_add, Schedule.scale_succ]; apply congr_arg; congr 1;ring
-- Elog subpower; no assumption about θ analytic disks in this result
lemma charging : RateLE atTop S' (P!) 0:=by
    intro r hr; obtain ⟨n,h⟩:= (tariff hw (r/2) (half_pos hr)).exists; let Sx:=Real.exp ((r/2)*(-S' n))
    filter_upwards [eventually_ge_atTop n,(Real.tendsto_exp_atTop.comp (C.S.divergent.const_mul_atTop (half_pos hr))).eventually_ge_atTop (P! n*Sx)] with i hi hp; let V:= Real.exp ((r/2)*S' i); have hv:P! n*Sx≤ V:= hp
    rw [Real.norm_of_nonneg (zero_le_one.trans (bounty_head _))]; calc
        _ ≤ P! n* Real.exp ((r/2)*(S' i-S' n)):= h i hi
        _ = (P! n*Sx)*V:=by rw [mul_assoc]; unfold Sx V; rw [←Real.exp_add]; ring_nf
        _ ≤ V*V:=mul_le_mul_of_nonneg_right hv (Real.exp_pos _|>.le)
        _ = _:= by unfold V;rw [←Real.exp_add]; ring_nf
lemma charging' : RateLE atTop S' (H!) 0:=by
   have he: RateLE atTop S' (fun i=> P! (i+1)) 0:=by
       let F:= (charging hw); let k(i):= S' (i+1); intro r hr
       have hp: ∀ᶠ i:ℕ in atTop, k i ≤2*S' i:=by -- neighboring scale assumption mesh
         have hv : Tendsto (fun i=> k i/S' i) atTop (𝓝 1):=((level_height (C:=C.S) tendsto_id).step C.path.levels.fits.mesh).pace; exact ((hv.eventually (ge_mem_nhds (by norm_num:(1:ℝ)<2))).and (C.S.divergent.eventually_gt_atTop 0)).mono (fun i hi=> (div_le_iff₀ hi.2).mp hi.1)
       filter_upwards [(tendsto_add_atTop_nat 1).eventually (F (r/2) (half_pos hr)),hp] with i hi hy; exact hi.trans (Real.exp_le_exp.mpr (by change r/2 * k i ≤_; nlinarith only [hy,hr]))
   apply RateLE.of_norm_le he; filter_upwards with i; rw [Real.norm_of_nonneg (zero_le_one.trans (grows _|>.2.2.2)),bounty_up]; exact le_mul_of_one_le_left (zero_le_one.trans (grows _|>.2.2.2)) (bounty_head _)
end YM.RG05Readout.Planes
