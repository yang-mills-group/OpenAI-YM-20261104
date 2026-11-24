import YM.RGComparison01.Plev
import YM.RGComparison01.Turnstile

/-!
# Boost and budget the distinguished inheritance pieces

 Use principal + other logarithm terms containing a *specified* group
 under the courier tolls. Recovers genuine contraction for the vacuum-
 regular tail of these, with still transition-specific currencies and
 AFTER-turn price; pre Exponent.<K needs no charging here; forced output
 still has joint-explicit budget>. No renewal or Hessian correction yet.

 Nontrivial: projection not among arbitrary periods, we need the *real*
 coarse step here. This sharper bound not claimed on auxiliary periods.
 -/

set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Ocean
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Control Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters Shoot Precision SectorMeasure Oriented Reserves
open ConnectedActivityE6.Blaze Blaze.March Captain Silica
open AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration
open Input Org Supply PriceCompiler Next.Scheduling Progress.DirectedRecipe
open PhysicalNext PhysicalNext.Repeat Height Song Time Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open Divides Selector Coin High Plev Brim Quests
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {X : Metals G} {D : Rolls X.p} {A : Alloy X D} (F : Roost.Factor A)
variable {m N n : ℕ} {R : Rep G (A.B.a.S.side (m+1) n)}
local notation "I" => A.B.a.clock.J m
local notation "J" => A.B.a.clock.J (m+1)
local notation "S" => (A.B.a.clock.op m n)
set_option quotPrecheck false
local notation "sizes" => (A.B.a.S.oneStep m n).exact_size
local notation "L₀" => (D.L J)
local notation "Q₀" => (F.target J I)
local notation "sP" => (X.p.profile I)
local notation "expn" => (F.expense J I)
local notation "θ₀" => (A.B.a.clock.hatBeta m)
local notation "t" => (F.t J I)
local notation "μ₀" => (F.shape.μ J I)
local notation "T" => (Pane.orchestra A N ((A.B.a.S.oneStep m n).exact_size))
local notation "θv" => betaF G θ₀ L₀
local notation "gZ" => Height.grow G L₀ θ₀
local notation "γ" => A.B.kin.alpha N m
local notation "p" => A.B.a.budget m
local notation "O" => Chi.canonical
variable (H : Boulevard.Chartlet F.shape A N m ((A.B.a.S.oneStep m n).exact_size) R)
local notation "aH" => (selfA H)
local notation "Y₀" => (Beam.marquee H p)
local notation "vk" => F.v J I
local notation "chargeE" => ((L₀).val:ℝ)⁻¹

-- provisional accumulating costs for forecast-E stages

def fee (m : ℕ) : ℝ := let j:= A.B.a.clock.J (m+1); let i := A.B.a.clock.J m
                           turnFee (A.B.a.budget m) * (F.v j i+2) / ((D.L j).val:ℝ)

variable (he : Quests.Gates F.shape A.delay) (hm : m < N)
    (hr : Quests.Posted F.shape F.v F.t F.recordP F.span F.prices F.menu A.delay)
    (hl : Travels A.B N (m+1) n R) (hb : R.beta∈band A.B.a (m+1))
    (Ω : ℕ→Prop) (e : ℝ) (he' : (Tithe.portion R.activities Ω).EBound R.p e)

include hm hr hb hl he'
lemma pristine (hx : e ≤ incomingE G L₀ θ₀) :
    1 ≤ F.v (A.B.a.clock.J (m+1)) (A.B.a.clock.J m) ∧
    Meadow.Budget p (Beam.dashboard H) (byLog (fun z : H.fragrances=>Inherited Ω z∧¬Height.tired H z) O)
      ((vk)/(L₀).val*e + chargeE * e) := by
  let u:= F.pledging
  have hy := F.pledging.conducts
  have Hc:N≥m+1:= hm
  have hstage:= step_paid A.B.a m
  have HK:= A.B.valid.pays m
  obtain ⟨hP,hG⟩ := hr _ _ HK _ hstage (first_le A.B.valid m)
  let desk := assigned hy.hearing.plan m n A.B N R
  have he₀ := (Psalm.Stage.directed hy.hearing (relieve A.B) hm hb hl (fun m' h'=> F.pledging.conducts.full _ _ _ (by simp at h'; omega))).1.enabled
  have hz₀:=he₀.make; obtain ⟨hp₀,hC⟩:= he₀.pre; have hf₀:=(he₀.clocks R.beta hb).2
  rw [← hl.point] at hz₀ hp₀ hC hf₀
  have hp:= params_eq A.B.valid m
  have hj:(p).power=(sP).power:=congr_arg RG.Stage.power hp
  obtain ⟨hx',ht,hu⟩:=F.pledging.agenda _ _ hstage
  obtain ⟨C,d,v,s,L,b,r,B,q,k,j',⟨K,-⟩,_,-⟩ := F.pledging.jewels _ _ HK _ hstage|>.2 _ _ _ T H.laws.data.funds (Pane.ovation A N sizes hm F.pledging.conducts.full) R H
  have he : 0 ≤ e:= by obtain ⟨f,h,hT⟩:=he'; exact budget_nonneg (hT 0)
  have hL := PriceCompiler.block_eq A.B.valid m
  have hF := hP T H.laws.data.funds R _ _ H p rfl hj hz₀ hu (hL ▸ hp₀) (hj ▸ hC) (hL ▸ hf₀) _ le_rfl C _ _ _ _ _ _ _ _ _ K Ω e he' he hx desk.broadCut desk.radius
  have hζ: preExponent p= (sP).supportExponent+3 := congr_arg (fun s:RG.Stage=>s.supportExponent+3) hp
  exact ⟨hC.nonneg,Divides.principal p rfl (hζ.trans_le (ht.trans (le_add_of_nonneg_right (by norm_num)))) hF⟩

include he
omit hl hb in
lemma others (u : ℝ) (hu : 1 ≤ u) (hx:u*e ≤ incomingE G L₀ θ₀) :
    Meadow.Budget p (Beam.dashboard H) (byLog (fun z : H.fragrances=>Inherited Ω z∧Height.tired H z) O)
      (u⁻¹ * chargeE * incomingE G L₀ θ₀) := by
  let V:= F.pledging; have hstage := step_paid A.B.a m; have HK:= A.B.valid.pays m
  obtain ⟨hP,hG⟩:= hr _ _ HK _ hstage (first_le A.B.valid m)
  let Y:= Tithe.bonus Ω u
  have ht : Tithe.Ticket R.activities R.p Y (2*incomingE G L₀ θ₀):= Tithe.portion_tickets _ _ _ _ _ _ (H.laws.data.funds.length_eq ▸ H.laws.intake.cap.labels.boundE) he' hu hx
  obtain ⟨hZ,C,d,v,S',k',b,r,B,q,i',l,⟨⟨K,hK⟩,hA,hT⟩⟩:= Plev.grants F sizes (H:=H) he hm ht 0 (Nat.zero_le _)
  obtain ⟨hg,hL,hY,hV⟩:= V.peak.large _ _ hstage θ₀ HK
  obtain ⟨ha,hv,hφ⟩:= hV B i' l hA K.balance hT
  have hw:= Beacon.spire_weighted K hg Y (gZ^3) (one_le_pow₀ hg) ht.1 hK (sP).power ha hY hv
  have hp:= params_eq A.B.valid m
  have hj:(p).power=(sP).power:=congr_arg RG.Stage.power hp
  have ht' : (p).order=(sP).order:=congr_arg RG.Stage.order hp
  have hz:= V.jewels _ _ HK _ hstage
  have hζ: preExponent p= (sP).supportExponent+3 := congr_arg (fun s:RG.Stage=>s.supportExponent+3) hp
  have hR := Divides.prices_hi p K (gZ^3) (one_le_pow₀ hg) hg Ω hu rfl rfl ht'.le hj.le
    (hζ.trans_le (V.agenda _ _ hstage).1) hL hz.1 hw
  apply Divides.loosen p hR
  let v:= Height.asset expn
  let a:=collars G v θ₀ (sP).order (sP).power
  let b:= salary Q₀ L₀ μ₀ B θ₀ (sP).order l
  obtain ⟨_,_,hQ',_⟩:= F.inn.chip _ _ HK _ hstage
  have hQ : (gZ^3)⁻¹*(a*(gZ*b*(1-1/2:ℝ)⁻¹)) ≤ Boulevard.gold G L₀ θ₀:= by rw [← mul_assoc]; exact hQ' B i' l hA K.balance hT
  rw [mul_inv,mul_assoc, mul_assoc u⁻¹ chargeE]; exact mul_le_mul_of_nonneg_left (hQ.trans hG) (inv_nonneg.mpr (by linarith only [hu]))

omit he hm hr hb hl he' in
lemma zero_offer {c : Side} {A:Type} (X : A → RegularAddress c) {U : A → Config G c → ℝ} {B : BudgetPoint}
    (h : ∀ s:ℝ, 0<s → Meadow.Budget B X U s) : Meadow.Budget B X U 0 := by
  obtain ⟨v,hv,hV⟩:= h _ zero_lt_one
  refine ⟨fun _=>0,fun i=> ?_,fun i=> ⟨(hV i).1,le_rfl,?_⟩⟩
  · simp [SumBudget]
  intro V hm l hl ha
  apply le_of_forall_gt_imp_ge_of_dense; intro s he
  obtain ⟨g,hg,hG⟩:=h s he
  have hv : B.mass (X i).support (g i) ≤ s:= by simpa only [↓reduceIte] using budget_single (Quotes.segment X (fun i=> (hG i).2.1) hg (X i).site) i
  exact (hG i|>.2.2 V hm l hl ha).trans ((B.loMass _ _ (hG i|>.2.1)).trans hv)

lemma contracts (hx:e ≤ incomingE G L₀ θ₀) : 0 ≤ fee F m ∧ Meadow.Budget p
    (Y₀).reg (fromPost F sizes R H (hires H Ω) γ).logRead (fee F m *e) := by
  obtain ⟨hF,hH⟩:= pristine F H hm hr hl hb Ω e he' hx
  have ht:= turnFee_pos p
  have heV : 0 ≤ e:= by obtain ⟨f,h,hT⟩:=he'; exact budget_nonneg (hT 0)
  let T₁ : H.fragrances→Prop := fun z=> Inherited Ω z
  let K:=(L₀).val
  have hy: 0 < (K:ℝ):=by unfold K; positivity
  have hA:0 ≤ vk+2:= by linarith only [hF]
  constructor
  · exact div_nonneg (mul_nonneg ht.le hA) hy.le
  have hL: Meadow.Budget p (Beam.dashboard H) (byLog (fun z : H.fragrances=> Inherited Ω z∧Height.tired H z) O) ((K:ℝ)⁻¹*e):= by
    rcases eq_or_lt_of_le heV with h|h
    · rw [← h,mul_zero]; apply zero_offer _; intro s hs
      let e₀:= incomingE G L₀ θ₀
      have hp: ∀ᶠ u:ℝ in atTop,u⁻¹*(K:ℝ)⁻¹*e₀ ≤ s:= by
        have h := ((tendsto_inv_atTop_zero.mul_const ((K:ℝ)⁻¹)).mul_const e₀)
        simp only [zero_mul] at h; exact (h.eventually (gt_mem_nhds hs)).mono fun u hu=> le_of_lt hu
      obtain ⟨u,hu,hξ⟩:= (hp.and (eventually_ge_atTop 1)).exists
      apply Divides.loosen p (others F H he hm hr Ω e he' u hξ ?_) hu
      rw [← h,mul_zero]; exact h.trans_le hx
    let u:= incomingE G L₀ θ₀/e
    have hu: 1≤ u:= (one_le_div h).2 hx
    apply Divides.loosen p (others F H he hm hr Ω e he' u hu (div_mul_cancel₀ _ h.ne').le)
    change u⁻¹ * (K:ℝ)⁻¹ * incomingE G L₀ θ₀ ≤ _
    rw [mul_right_comm,inv_mul_eq_div]; apply le_of_eq; unfold u; clear hu
    field_simp [(lt_of_lt_of_le h hx).ne']
  have h := budgets_union p hL hH
  have hv : (fun z:H.fragrances=> (Inherited Ω z ∧ Height.tired H z) ∨ (Inherited Ω z ∧ ¬Height.tired H z))=Inherited Ω := by ext; grind
  rw [hv] at h
  apply Divides.loosen p (post_fee F sizes R H (hires H Ω) γ (needle Ω p γ h))
  change _ ≤ (turnFee p*(vk+2)/(L₀).val)*e; unfold K; apply le_of_eq; ring
end YM.RGComparison01.Ocean
