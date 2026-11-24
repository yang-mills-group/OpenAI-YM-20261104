import YM.Integration.WilsonOlderFreshConnectedRobe
import YM.Integration.OriginalBareMarkedInvoice
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshConnectedCurrency
open Function Filter Finset MeasureTheory Lattice RG Precision Wilson Tree Exterior
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.Express WilsonCoeffUV.Embroider
open WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Soil WilsonCoeffUV.Wheel.Flooring
open Work.F08
open scoped BigOperators Classical


open FundedMarkedPathSelection
open PhysicalNext.Repeat.Legato WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Embroider.Canvas
open ComparisonDensity.Address WilsonCoeffUV.Shard WilsonCoeffUV.Winding OriginalIssuedMarkedRows
open ActualRunAdmissionScales OriginalBareMarkedInvoice Filter Function
open WilsonOlderFreshConnectedRobe WilsonCoeffUV.Bank.Ticket
open scoped Topology
variable {G:Gauge}{n e m N l b t:ℕ}{A:ℝ}{k D:Fin n → ℕ}{S J:Finset (Fin n)}{c:Fin n}

def credit (G:Gauge)(D k:Fin n → ℕ)(J:Finset (Fin n))(c:Fin n)(e l:ℕ):Credit:=
  ((pur (glacier G l (e+1))).prodC Credit.leanC).prodC
    ((vigor G D k e Credit.leanC Credit.leanC).prodC (OriginalBareMarkedInvoice.addresses J c))

theorem charged (l : ℕ) (Q : Realm G (e+1) Credit.leanC) (hm : Q.anchor  ≤  m) (ho : c ∈ J)
    (tickets : Insure b t Q Credit.leanC) (A : ℝ) (hA : 0  ≤  A) :
    glacier G l (e+1) * VestZ b t Q m hm * price Q k D A J m *
      sprigs J c (Vσ Q m hm)  ≤  Q.cash (credit G D k J c e l) m * A^J.card := by
  let V := vigor G D k e Credit.leanC Credit.leanC
  let T := pur (glacier G l (e+1))
  have cash (B : Credit) : 0  ≤  Q.cash B m := zero_le_one.trans (Credit.purchase _ (Q.depth m hm))
  have z : 0  ≤  VestZ b t Q m hm := zero_le_one.trans (tickets.proof m hm).tag
  have roots : 0  ≤  sprigs J c (Vσ Q m hm) :=
    cap_nn (sprigsPay ho (0 : Cover) (perk hm))
  have rootBill : sprigs J c (Vσ Q m hm)  ≤  Q.cash (addresses J c) m :=
    punchWorth J c b t Credit.leanC tickets hm
  have fieldBill : glacier G l (e+1) * VestZ b t Q m hm  ≤ 
      Q.cash T m * Q.cash Credit.leanC m :=
    mul_le_mul (pure_goal _ _) (tickets.labor m hm).2 z (cash _)
  have rest := mul_le_mul_of_nonneg_left rootBill (cash V)
  calc
    _ = ((glacier G l (e+1) * VestZ b t Q m hm) *
        (Q.cash V m * sprigs J c (Vσ Q m hm)))*A^J.card := by unfold FundedMarkedPathSelection.price; ring
    _  ≤  ((Q.cash T m * Q.cash Credit.leanC m) * (Q.cash V m * Q.cash (addresses J c) m)) * A^J.card :=
      mul_le_mul_of_nonneg_right (mul_le_mul fieldBill rest (mul_nonneg (cash V) roots)
        (mul_nonneg (cash T) (cash _))) (pow_nonneg hA _)
    _ = _ := by simp only [credit, Realm.cash, Credit.products, T, V]

private theorem subpower (c:ℝ)(hc:0 ≤ c)(n:ℕ){δ:ℝ}(pos:0<δ):
    ∀ᶠ x:ℝ in atTop,c*(1+Real.log (Real.log x))^n  ≤  x^δ:=by
  have small:=(isLittleO_log_rpow_rpow_atTop (n:ℝ) pos).def (show 0<1/(1+c) by positivity)
  filter_upwards [small,Real.tendsto_log_atTop.eventually_ge_atTop 1,eventually_gt_atTop (0:ℝ)]
    with x h hl hx
  have lp:0<Real.log x:=by linarith
  have zp:0 ≤ (1+Real.log (Real.log x)):=by
    have:=Real.log_nonneg hl;linarith
  have zl:(1+Real.log (Real.log x))  ≤  Real.log x:=by
    linarith [Real.log_le_sub_one_of_pos lp]
  have val:(Real.log x)^n  ≤  (1/(1+c))*x^δ:=by
    change ‖(Real.log x)^(n:ℝ)‖  ≤  (1/(1+c))*‖x^δ‖ at h
    simpa only [Real.rpow_natCast,Real.norm_of_nonneg (pow_nonneg lp.le _),
      Real.norm_of_nonneg (Real.rpow_nonneg hx.le _)] using h
  calc
    _  ≤  c*(Real.log x)^n := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ zp zl _) hc
    _  ≤  (1+c)*((1/(1+c))*x^δ) := mul_le_mul (by linarith) val (by positivity) (by positivity)
    _ = _:=by field_simp


theorem tariff (R:Run G)(simple:G.Simple)(V:Credit){δ:ℝ}(pos:0<δ):
    ∀ᶠm:ℕ in atTop, V.buy (zz R.family.path.levels m) ≤ (R.family.path.levels.clock.hatBeta m)^δ:=by
  have growth:Tendsto R.alloy.B.a.clock.hatBeta atTop atTop:=tendsto_atTop_add_const_left _ _
    (R.family.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos simple))
  exact growth.eventually (subpower V.x (zero_le_one.trans V.good) V.d pos)

theorem posted (Q:Realm G (e+1) Credit.leanC)(hm:Q.anchor ≤ m)(X:Input Q hm S k D A)
    {s u v:ℝ}{o:Cover}{j:ℕ}{r:Fin (l+j+1)}(p:Rooted Q hm X J c l N s u o j r)(h:u ≤ v):
    Rooted Q hm X J c l N s v o j r:=by
  obtain ⟨μ,born,fields,raw,dress⟩:=p
  refine ⟨μ,born,fields,⟨raw.1,raw.2.1,raw.2.2.trans h⟩,?_⟩
  intro g hg h1
  have d:=dress g hg h1
  exact ⟨d.1,d.2.1,d.2.2.trans (mul_le_mul_of_nonneg_left h (zpow_pos hg _).le)⟩

theorem purchased (R:Run G)(simple:G.Simple)(l:ℕ){δ:ℝ}(power:0<δ):
    ∀ᶠm:ℕ in atTop,∀(Q:Realm G (e+1) Credit.leanC)(hm:Q.anchor ≤ m)(_reported:Q.y=zz R.family.path.levels)
      (N:ℕ)(X:Input Q hm S k D A)(_sub:J⊆S)(_pin:c∈J)(_pos:0 ≤ A)(_live:m<N)
      (_closed:Cloze D k Q Credit.leanC)
      (_rank:∀y n,WilsonCoeffUV.Blue.shellK l ((output X J N y).1 n))
      (_tickets:Insure b t Q Credit.leanC)(_count:J.card ≤ b)(_seat:l ≤ t),
    (∀y,Rendered Q hm X J c l N y) ∧ ∀o j,j ≤ e → ∀r:Fin (l+j+1),
      Rooted Q hm X J c l N (VestS b t Q m hm) ((R.family.path.levels.clock.hatBeta m)^δ*A^J.card) o j r:=by
  filter_upwards [tariff R simple (credit G D k J c e l) power] with m cash
  intro Q hm reported N X sub pin pos live closed rank tickets count seat
  obtain ⟨film,words⟩:=WilsonOlderFreshConnectedRobe.issued Q hm X sub pin pos live closed rank tickets count seat
  refine ⟨film,fun o j hj r=>posted Q hm X (words o j hj r) ?_⟩
  have quote:=charged (k:=k) (D:=D) l Q hm pin tickets A pos
  have used:Q.cash (credit G D k J c e l) m ≤ (R.family.path.levels.clock.hatBeta m)^δ:=by
    simpa only [Realm.cash,reported] using cash
  exact quote.trans (mul_le_mul_of_nonneg_right used (pow_nonneg pos _))

theorem original (R:Run G)(simple:G.Simple){δ:ℝ}(power:0<δ):
    ∀ᶠm:ℕ in atTop,∀(Q:Realm G (e+1) Credit.leanC)(hm:Q.anchor ≤ m)(_reported:Q.y=zz R.family.path.levels)
      (N:ℕ)(X:Input Q hm S k D A)(_sub:J⊆S)(_pin:c∈J)(_pos:0 ≤ A)(_live:m<N)
      (_closed:Cloze D k Q Credit.leanC)(_tickets:Insure b t Q Credit.leanC)(_count:J.card ≤ b)(_seat:mass k J ≤ t),
    (∀y,Rendered Q hm X J c (mass k J) N y) ∧ ∀o j,j ≤ e → ∀r:Fin (mass k J+j+1),
      Rooted Q hm X J c (mass k J) N (VestS b t Q m hm) ((R.family.path.levels.clock.hatBeta m)^δ*A^J.card) o j r:=by
  filter_upwards [purchased (S:=S) (J:=J) (c:=c) (A:=A) (k:=k) (D:=D) (e:=e) (b:=b) (t:=t)
    R simple (mass k J) power] with m sale
  intro Q hm reported N X sub pin pos live closed tickets count seat
  exact sale Q hm reported N X sub pin pos live closed (fun y=>(ready X sub pos live closed y).1.span) tickets count seat

end YM.Integration.WilsonOlderFreshConnectedCurrency
end
