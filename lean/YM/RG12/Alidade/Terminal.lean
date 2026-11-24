import YM.RG12.Alidade.Purse
import YM.RG12.Alidade.Office
/-!
# Priced connector & cumulative criterion. Inputs: local cards `Office` at lit k,
calendar Slurry and passcost insurance, same t(k) at all nodes eventually decreasing,
normalized adjacent frame & *scalar* price on LOCAL two-leg measurements, k-chart filter.
No dyads or continuum lifts required in this criterion. Not assumed from master comparison;
further consumers interpret the scalar criterion and exhibit these cards on the Construction
with quantitative flavor (and identify Leak hypothesis from two/three orders of comparison
without full IR transforms).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Alidade
open Function Set Finset Filter RG Wilson Lattice Real Frames Commission Rail
open scoped Topology BigOperators Classical

variable {G:Gauge}{C:Family G}{M:∀ d,ℕ→RepChart C d}{S:Table C.book}{B:DiffPlan S}
local notation "Z!"=> C.path.levels
local notation "χ"=> C.path.levels.clock.hatBeta
local notation "a!"=> C.S.a
local notation "clk"=>epoch C.path.levels
variable {d:ℕ}{V:Grade d→Type}[∀ i,NormedAddCommGroup (V i)][∀ i,NormedSpace ℂ (V i)][FiniteDimensional ℂ (Col V)]
variable {Y : ℕ → Col V ≃ₗ[ℂ] S.Field d} {P:Col V ≃ₗ[ℂ] S.Field d} {g:ℕ→S.Field d→ℝ}{t e:ℕ→ℝ}{f:ℕ→ℕ}{c:ℕ→Prop}

variable (hG:G.Simple)(h: Beacon C.path.levels f c)(hr: Slurry C.path.levels)
include hG h hr
lemma insured_distance (D:ℝ) : ∀ᶠ k in atTop, let Z:=C.path.levels.clock; let w:=radar (Z.hatBeta (k+1)) (Z.J k)
      (Z.monitor (f k) ≤ w ∧ Z.monitor (k+1) ≤ w) ∧
      C.S.a (f k)/ C.S.a (k+1) ≤ w^2 ∧ D ≤ w:=by
  let s:=C.path.levels; let L(k):= s.clock.monitor k
  filter_upwards [h.valid,h.grows.eventually (monitor_control s hG), (vast s hG hr).eventually_ge_atTop D,eventually_gt_atTop (0:ℕ)] with k hk hM hz hf Z w
  have he : passcost s k ≤ w:= radar_later (delay s k) (year_mono s hG (Nat.le_succ k)) le_rfl
  have hw: 1≤ w:= radar_big (delay s _) _
  have hz':L (k+1) ≤ w:= by
    have ht:= licensed s hr (k+1) (Nat.succ_pos k)
    exact ht.trans (radar_later (delay s _) le_rfl (s.fits.mono (Nat.le_succ k)))
  refine ⟨⟨(hM (k+1) (hk.1.trans (Nat.le_succ k))).trans hz',hz'⟩,?_,hz.trans he⟩
  have hQ: ((s.S.block k).val:ℝ)≤w:= (hr k).1.trans (radar_later (delay s k) (year_mono s hG (Nat.le_succ k)) (s.fits.mono (Nat.le_succ k)))
  let i:=f k
  change (a! i)/(a! (k+1)) ≤ _
  rw [Schedule.a_step,div_div_eq_mul_div,sq,mul_div_right_comm]
  -- identify ratio
  exact mul_le_mul (hk.2.2.2.trans he) hQ (Nat.cast_nonneg _) (zero_le_one.trans hw)

variable (hC:C.Makes){φ:Filter UVIndex}[φ.NeBot](hV:Observing C hC φ M)
variable {s:ℕ}{K:ℝ}
-- inputs at late cells only
variable (hx:∀ᶠ i in atTop,c i→ Office M B P (Y i) (g i) (t i) i s K)(ht:∀ᶠ i in atTop,t (i+1) ≤ t i)
variable {p b:ℕ}
-- Accommodate at most polynomial in SCALE per local shear/opnorm, leaves prices in purse
abbrev pursePower (d p b:ℕ):=d*(p+b+4+1)+(p+d+1)
structure Clearing (Z:Levels G) (Y:ℕ → Col V≃ₗ[ℂ] S.Field d) (g:ℕ→S.Field d→ℝ)(t e:ℕ→ℝ)(p b:ℕ)(c:ℕ→Prop)(K:ℝ): Prop where
    pocket : ∀ i, e i ∈ Set.Icc 0 1
    prices : ∀ᶠ i in atTop, c i→ c (i+1)→∃ ha:0 < t i/t (i+1), Near Z e p b (pursePower d p b) i (Y i) (Y (i+1)) (g i) (g (i+1)) K _ ha

omit h hG hr in
lemma weakly_after (t:ℕ→ℝ)(hx:∀ᶠ i in atTop,t (i+1) ≤ t i) : ∀ᶠ i in atTop, ∀ j,i ≤ j→ t j ≤ t i:=by
   obtain ⟨N,hN⟩:= eventually_atTop.mp hx
   filter_upwards [eventually_ge_atTop N] with i hi j hj
   induction j,hj using Nat.le_induction with
   | base=>exact le_rfl
   | succ j hj he=> exact (hN j (hi.trans hj)).trans he
include hC hV hx ht
theorem journey (H:Clearing (Z!) Y g t e p b c K) (hf:∀ i,0 < t i):
    ∃ Q:ℕ,Tariff (Z!) f c Y P t (fun i=>compress (g i∘Y i)) e K (pursePower d p b) Q (p+b+4):=by
   let D:=pursePower d p b; let b':=p+b+4
   have h0:∀ i,0≤e i:= fun i => (H.pocket i).1; have h1:∀ i,e i ≤ 1:= fun i=> (H.pocket i).2
   let q:=1+2*(d+1)+s+(2+s)*d;refine ⟨1+q,h,h0,hf,hx.mono fun i hi h=>⟨fits_compress (hi h).costs,(hi h).wage⟩,?_⟩
   have hK:∀ᶠ i in atTop, K ≤ epoch (Z!) i:= (epoch_late (Z!)).eventually_ge_atTop K
   let τ : ℝ:= (↑d+1)*K^2
   let A₀:= (Z!).clock
   filter_upwards [hx, (tendsto_add_atTop_nat 1).eventually hx,h.grows.eventually hx,h.grows.eventually (weakly_after t ht), insured_distance hG h hr τ,H.prices, step_factor_small (Z:=Z!) h1,h.valid, ht,hK,
     h.grows.eventually ((Finset.range (d+1)).eventually_all.mpr (fun i _=> eventually_ge_atTop (C.ref i)))] with k ha hb hj hT he hx hs hw hT₀ hz hf lit
   have bL:= hb lit
   refine ⟨fun hL => ?_,fun hL => ?_⟩
   · obtain ⟨hr,hX⟩:=hx hL lit
     exact ⟨hr,(one_le_div (by have he:=bL.times.1; exact (C.S.a_pos (k+1)).trans_le he)).mpr hT₀,fun v=> near_prices hG h0 hX hz hs v (1+q)⟩ -- J arg
   let j:= f k; let W:=radar (A₀.hatBeta (k+1)) (A₀.J k); let X:=Y j
   have hi':j ≤ k+1:=hw.1.trans (Nat.le_succ k)
   obtain ⟨⟨h2,h1⟩,h3,h4⟩:=he
   have hW:1 ≤ W:= radar_big (delay (Z!) _) _
   have hp :=fun i hi=> hf i (Finset.mem_range.mpr (Nat.lt_succ_of_le (show i ≤ d from hi)))
   have bL' :=hj hw.2.1
   obtain ⟨hr,H⟩:=round_trip bL hC hV j hi' hp bL' (W^2) W (one_le_pow₀ hW) (not_lt.mpr hW) h3 h2 h1 (hT _ hi')
   refine ⟨hr,(one_le_div ((C.S.a_pos _).trans_le (bL.times.1))).mpr (hT _ hi'),?_⟩
   intro v T A
   have hA := pace_form (Y j) (Y (k+1)) bL'.wage bL.wage hr
   refine bridge_prices (a:=q) (b:=p+b+4) (D:=pursePower d p b) hG h0 (fits_compress bL'.costs) (fits_compress bL.costs) hA (triangular.inv hA) hi' (m:=A₀.J k) (by have hx:=hw.2.2.1 hL; change A₀.J (f k)+1= A₀.J k at hx; change A₀.J (f k) < A₀.J _; omega) ((Z!).fits.mono (Nat.le_succ k)) (fun x=> ?_) h4 (by unfold pursePower; omega) v -- s arg?
   obtain ⟨hx,he⟩:= H x;let B:= ((d+1:ℕ):ℝ)*K^2
   have ht0 : B ≤ W:=by simpa only [τ,Nat.cast_add,Nat.cast_one,B] using! h4
   have he' : B*(W^2)^(d+1)*W^s*(W^2*W^s)^d*‖x‖ ≤ W^q*‖x‖:=by
      have hh:0 ≤ W:=zero_le_one.trans hW; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      unfold q; simp only [pow_add,pow_mul,pow_one]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ht0 (by positivity)) (pow_nonneg hh _)) (pow_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg hh _)) _)
   exact ⟨hx.trans he',he.trans he'⟩

end YM.RG12.Alidade
