import YM.RG04B.Vac.Small

/-!
# Uniform physical closure of the unmarked iteration

Consumes qev in precisely the needed layout: on any **same-class input**
supply remodeled reps, fixed support/price/threshold from C.path, canonical/
matched slots present at these addresses, value/affine-null inherited error.
The local RG estimate owed gives an *exact representation* with the stored
bills: `f = C_J` pre costs, `afterPrice` covers p_i^geo, `localLoss` a
post-block o(1) booked before constructing. The settled EBound includes
possible reset price f times that before-extraction cost, post cubics' t^3 *
abs(beta error) price, singular g^(-rank) price even on the spatially-flat
calibration to the actual β (we choose to leave that offset in the kinetic
alongside beta from C, see Remodeled). qev's before-extraction price `charge`
and ω_e absorption may already include the `Y.beta` conversion in last local
moves (flat) if powered into b under that inequality. Other constants can be
allocated pre/post etc by the producers. Keep K and output density incl scalar;
packing labels and `tagged` choice must also set up the right MARKED continuation
on this same output. Can add producer witnesses (strong forced reserve for
attachment, etc) in the path `conjoint` consumed later. Nothing below proves
these LOCAL (RG01--3,4A) analytic estimates. In particular `OrderedStart`'s
row/omega inputs are *of* the unmasked formal (WilsonX Fk) data to be supplied;
we have no claim any arbitrary container `Render` is WilsonX. Don't use parent
`forecast` or define a WilsonX series by reading kinetic off R.

What is not assumed here is applicability from start to stop on the actual
path! This RG04B producer proves propagation with cutoff-uniform constants,
all gates/vacuum identity retained, payment of the uncertain reset (hence
kres at every step including on entering different smoothing indices). This
uses RG01+, RG03+, RG04A local estimates, not BOOKED into construction; they
must provide the concrete hypotheses of `Step` and use their assumed
support/payment costs, not an unrelated step recipe on a different cutoff or
norm. Re-expression to make those hypotheses is exactly their task. Recurrence
proof never calls RG analyticity on unknown e.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 3000
namespace YM.RG04B.Vac
open Function Filter Set Lattice RG Real Wilson PhysicalNext.Repeat.Legato
open scoped Topology Classical BigOperators Matrix.Norms.Frobenius

variable {G : Gauge}

/-- Supplemental local witness: e.g. relationship on path books/overlay
alphabets. Passed back UNCHANGED at each step for use in the marked iteration,
so local suppliers can use the *same* outputs. Clients specify this part. -/
abbrev Conjoint (C : Family G) := ∀ (_N p m:ℕ), Rep G (C.side (m+1) p) → Rep G (C.side m p) → Prop

variable {C : Family G}

set_option quotPrecheck false
local notation "P" => C.path.levels
local notation "L" => ratio C.path.levels
local notation "B" => C.path.levels.clock
local notation "S" => C.path.levels.params
local notation "T'" => temporal C.path.levels
local notation "X" => C.path.rep

/-- BudgetPoint (levels implied by p,N,m) and input g shared. `before` is the
bound consumed *from* qev after alignment, `keep` includes reclosure and
kinetic/β-correction. Not making any claim about affine conditions on raw
pre-reset labels. Requested `e≥2`, `τ` announced loss. -/
structure Step (M : Render C) (e N p m : ℕ) (Xf : Rep G (C.side (m+1) p))
    (Y : Rep G (C.side m p)) (r b c f h u : ℝ) (k : ℕ) : Prop where
  /-- `r` in, `b` qev (before uncertain extraction), `c` settled. -/
  initialPay : 0≤b
  before : let G₁:=gAt C N p (m+1)
           b ≤ (f/L m + h)*r + u*(G₁^(e+1)+G₁⁻¹^k * |Xf.beta-(X N p (m+1)).beta|)
  kinetic : (T' m)^2 * |Y.beta-guess M e N p m| ≤ f*b
  keep : let G₁:=gAt C N p (m+1)
         c ≤ f*b + u*(G₁^(e+1)+(T' m)^3 * |Y.beta-guess M e N p m| + G₁⁻¹^k * |Y.beta-(X N p m).beta|)
  passed : 0 ≤ c ∧ Sliced M N p m e Y c

/-- **Input** from the local estimates (incl WilsonX calculation and reset).
Economics, geometry and branch permissions must be paid by those producers. Slot
`U` arbitrary *post* price, with a `Budgeted` receipt (see e.g. livingPrices,
Fees.reserve for getting them). `K` controls possibly needed smallness of
calibration beta to call it. *Every* m+1 in tail above any report mesh, no
choice of other auxiliary path assumed.* Doesn't presume history already
carries comparison data to m+1 -- only local on a class, incl any required
properties of M as coming from the formal producer. -/
def LocalPay (M : Render C) (e : ℕ) (τ : ℝ) (D : Drag) (F : Fees) (i : ℕ) (U : ℕ→ℝ) (K k : ℕ)
    (tagged : Conjoint C) : Prop := ∀ᶠ m in atTop, ∀ N p : ℕ, m < N →
      ∀ Xf : Rep G (C.side (m+1) p), ∀ r : ℝ, 0 ≤ r → Sliced M N p (m+1) e Xf r →
        r ≤ money C e N p (m+1) τ → |Xf.beta-(X N p (m+1)).beta| ≤ gAt C N p (m+1) ^ K →
          ∃ (Y : Rep G (C.side m p)) (b c : ℝ), Step M e N p m Xf Y r b c
            (firstBill F P i m) (slowing D i P m) (U m) k ∧ tagged N p m Xf Y

abbrev kiosks (g : ℝ) (n : ℕ) (τ : ℝ) := g ^ ((n:ℝ)-1-τ)

section
/-- Step closes even retaining a strict contraction price (so downstream
estimates can, e.g., pay with identical eta on the history and only extract
the extra inverse powers needed for the reset). -/
theorem sealed (hC : C.Makes) (hG:G.Simple) {D : Drag} {F : Fees} (hs : stripe F P)
  (ht : Booked D.fund P) (hk : Booked requireConversion P) (M : Render C) (e : ℕ) {u : ℕ→ℝ}
  (hU : Budgeted P u) (i k : ℕ)
  {τ : ℝ} (hr : 0 < τ) (hτ : τ ≤ 1/2) (he : 2≤e) :
    ∀ᶠ m : ℕ in atTop, ∀ N p, m<N → ∀ (x : Rep G (C.side (m+1) p)) (y : Rep G (C.side m p)) (r b c : ℝ),
      0≤r → Remodeled C N p (m+1) x → r ≤ money C e N p (m+1) τ →
        Step M e N p m x y r b c (firstBill F P i m) (slowing D i P m) (u m) k →
        c * toll P m ≤ money C e N p (m+1) τ ∧ c ≤ money C e N p m τ ∧
          |C.path.β N p m - guess M e N p m| ≤ kiosks (gAt C N p (m+1)) e τ := by
  have hz := boughtToll hs
  have H:Budgeted P (fun j=> toll P j * firstBill F P i j):= hz.mul (index_spend hs i).1
  have hvac:=debts hC hG hs hk k e hr (show 0<(1:ℝ)/64 from by norm_num) (H.mul hU)
  have hwn:=debts hC hG hs hk k e hr (show 0<(1:ℝ)/4 from by norm_num) (hz.mul hU)
  have h:= vanishT hC hG u zero_lt_one hU
  have hl: e≥ (2:ℝ) := by exact_mod_cast he
  filter_upwards [h,hvac,hwn,fades hs D ht i (show 0 < (1:ℝ)/64 from by norm_num), shift_marker hC hG hs hk e (show 0<(1:ℝ)/2 from by norm_num),
    downhill hC hG, (tendsto_add_atTop_nat 1).eventually (coupling_exit hC hG (c:=1) zero_lt_one),(show ∀ᶠ i in atTop, 0 ≤ u i from by obtain ⟨_,_,_,hx⟩:=hU; exact hx.mono fun i h => h.1)]
    with j ht hp ht' hy hb hM hF hV N p hN x y r b c h₀ he' hx step
  obtain ⟨hx',hT,hβ,hc',hv,hpay⟩:=step
  let g:= gAt C N p (j+1)
  let E:= money C e N p (j+1) τ
  have hG' : 0<g:= running_pos hC _ _ _ hN
  have hE : 0 < E:= Real.rpow_pos_of_pos hG' _
  let T:= T' j; have hT₀:0<T:= (P|>.budget _).threshold_pos
  let d:= |y.beta-guess M e N p j|
  let A:=g⁻¹ ^k * |x.beta-C.path.β N p (j+1)|; let Q:=g⁻¹ ^k * |y.beta-C.path.β N p j|
  have hw : 0≤u j := hV
  have hf : 0 ≤ firstBill F P i j:= zero_le_one.trans (atLeastOne F P i j).1
  have hu : 0≤ toll P j := zero_le_one.trans (toll_one _)
  obtain ⟨-,hX,hB⟩:=hp N p hN; obtain ⟨hY,-,hD⟩:=ht' N p hN
  have hB₀: toll P j * firstBill F P i j * b ≤ (1/16)*E:=by
    change b ≤ _*r + u j*(g^(e+1)+A) at hT
    change toll P j*firstBill F P i j*u j*g^(e+1) ≤ _*E at hB
    have hL₁: toll P j*firstBill F P i j*(firstBill F P i j / L j+slowing D i P j) *r ≤ (1/64)*E :=
      le_trans (mul_le_mul_of_nonneg_right hy h₀) (mul_le_mul_of_nonneg_left hx (by norm_num))
    have hL₂ : toll P j*firstBill F P i j*u j*A ≤ (1/64)*E := hX x he'
    linarith only [mul_le_mul_of_nonneg_left hT (mul_nonneg hu hf),hL₁,hL₂,hB,hE]
  have hC₀ : c * toll P j ≤ E := by
    change T^2*d ≤ firstBill F P i j*b at hβ
    have hp: u j*T^3*d*toll P j ≤ (1/16)*E:= by
      change u j*T ≤ 1 at ht
      have hw := mul_le_mul_of_nonneg_left hβ (mul_nonneg (mul_nonneg hw hT₀.le) hu)
      have hE' := mul_le_mul_of_nonneg_right ht (mul_nonneg hu (mul_nonneg hf hx'))
      linarith only [hw,hE',hB₀]
    change c ≤ _ + u j*(g^(e+1)+T^3*d+Q) at hc'
    have hx := mul_le_mul_of_nonneg_right hc' hu
    have hvT: toll P j*u j*Q≤(1/4)*E:=hY y hpay.same
    change toll P j * u j * g^(e+1) ≤ (1/4)*E at hD
    linarith only [hx,hB₀,hp,hvT,hD,hE]
  refine ⟨hC₀,le_trans ((le_mul_of_one_le_right hv (toll_one _)).trans hC₀)
    (Real.rpow_le_rpow hG'.le (hM _ p hN) (show (e:ℝ)+1-τ≥0 by linarith)),?_⟩
  have hR : T^2*d ≤ (1/16)*E:= by
    apply le_trans hβ
    calc
      _ ≤ toll P j*(firstBill F P i j*b) := le_mul_of_one_le_left (mul_nonneg hf hx') (toll_one j)
      _ ≤ _ := by linarith only [hB₀]
  have hK : E = g^2*kiosks g e τ := by
    unfold E money zone kiosks
    change g ^ ((e:ℝ)+1-τ) = _
    rw [← Real.rpow_natCast,← Real.rpow_add hG']; congr 1; push_cast; ring
  have hl:(g/2)^2*d ≤ (1/16)*E := by
    have ht : g ≤ 2*T:= (hM _ p hN).trans ((thresholdHat hC hN.le (p:=p)).2)
    apply (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (half_pos hG').le (show g/2≤T from by linarith) 2) (abs_nonneg _)).trans hR
  have hz : 0 ≤ kiosks g e τ := Real.rpow_nonneg hG'.le _
  have hr: d ≤ (1/2)*kiosks g e τ := by
    apply le_of_mul_le_mul_left _ (sq_pos_of_pos hG'); linarith only [hl,hK,hE]
  have hl:g^e≤kiosks g e τ:= by
    rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_ge hG' (hF _ p hN) (by linarith only [‹0<τ›])
  have hy : |y.beta-C.path.β N p j| ≤ 1/2*kiosks g e τ :=
    (hb _ p hN y hpay.same).trans (mul_le_mul_of_nonneg_left hl (by norm_num))
  rw [abs_sub_comm] at hy
  have hA: |C.path.β N p j- guess M e N p j| ≤ |C.path.β N p j-y.beta|+d := by
    rw [show C.path.β N p j-guess M e N p j=C.path.β N p j-y.beta + (y.beta-guess M e N p j) by ring]; exact abs_add_le ..
  unfold d at *; linarith only [hA,hy,hr]
end
end YM.RG04B.Vac
