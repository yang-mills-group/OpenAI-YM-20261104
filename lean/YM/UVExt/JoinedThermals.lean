import YM.UVExt.ThermalEmber
import YM.UVExt.WakeCommerce
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Lambent

/-!
# Magpie -- recycling actual Utopia revenue on the finite, BOTH-sided probe budget

New balance sheet for comparison estimates, not an admission changing the original Shoot labels.
Holding all noncoupling arguments here still, including clipping masks and thresholds. Heat
trials use d derivative environments spaced by iteration-independent levels.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVExt.EnergyRay.Thermal.Account
open Function Lattice RG Pressure Pressure.Stores Pressure.Tube Wilson Finset MeasureTheory Tree
open Filter Set ConnectedActivityE6 Gaussian Coat Pulse Blaze Silica Raw Precision
open Push Push.AbsoluteSums Push.SectorMeasure Push.SectorMeasure.Oriented Reserves Footprint
open scoped Topology Classical BigOperators ContDiff
variable {κ : Type*} {c f L : Side} {s:κ→Support c} {w d:κ→ℝ} {B:ℕ} {ε x b : ℝ}
variable {G:Gauge} {S:StepData c f} {P : Teller G} {T : Tube G S} {R:Rep G f}
variable {Q : ConnectedActivityE6.Target G P} {W:Molecule S→ℝ} {n : ℕ} {u a η μ D C τ δ v r C' : ℝ}{t : ℂ}{o:Target.Order G u}{χ:Chi}
open Mixed.Costs

def gross (s:κ→Support c) B w d ε x b := Ac.Hit s B (tariff w d (fun _=>0) ε) x b
private lemma enrich {A E : Type*}[Fintype A] {f:A→E→ℝ}{c:A→ℝ}(rate:A→ℝ) (h:∀ i, SumBudget (f i) (c i)) (he:∀ i,0≤rate i): SumBudget (fun j=>∑ i,rate i*f i j) (∑ i,rate i*c i):=by
    have hF := fun i:A=>((h i).2.1.hasSum.mul_left (rate i))
    have hh:=hasSum_sum (s:=Finset.univ) (fun i (_: i∈Finset.univ)=> hF i)
    exact ⟨fun j=>sum_nonneg (fun i _=>mul_nonneg (he i) ((h i).1 j)),hh.summable, hh.tsum_eq.le.trans (sum_le_sum fun i _=> mul_le_mul_of_nonneg_left (h i).2.2 (he i))⟩
lemma heat_budget {f:ℝ→κ→ℝ}(h : ∀ i j:Fin (n+1), gross s B (f (nodes t δ i j)) d ε x b) :
    let uu i := cash t (δ:=δ) (n:=n) (f · i)
    gross s B uu d ε x ((1+speed n^n * (2*(n+1):ℕ))*b) := by
    intro uu p; let tilt (g:κ→ℝ) (i:κ):= if p∈s i then tariff g d (fun _=>0) ε i*Real.exp (x*coverNumber B (s i)) else 0
    let idx (i:Fin (n+1) × Fin (n+1)) := f ((nodes t δ (n:=n)) i.1 i.2); let ty:Type:= Option (Bool × Fin (n+1))
    let χ : ty→ Fin (n+1) × Fin (n+1) := fun i=>match i with | some (true,z) => (z,0)| some (false,z) => (0,z)| none=>(0,0)
    let flag (i:ty):= tilt (idx (χ i)); let fee (i:ty) := if i = none then 1 else speed n^n; have he i : 0≤fee i := by dsimp [fee,speed]; split_ifs <;> positivity
    have hp' i : SumBudget (flag i) b := by dsimp [flag,idx,tilt]; exact h (χ i).1 (χ i).2 p
    have hv:= enrich (f:=flag) (c:=fun _=>b) fee hp' he
    have hg (g : Fin (n+1) × Fin (n+1) → ℝ): ∑ i, fee i*g (χ i) = g (0,0) + speed n^n*∑ i, (g (i,0)+g (0,i)):= by
       unfold fee
       rw [Fintype.sum_option]; simp only [if_pos,one_mul, Option.some_ne_none, ite_false,χ]; change g (0,0)+ (∑ p:Bool × Fin (n+1), speed n^n*g (χ (some p)))= _
       rw [Fintype.sum_prod_type,Fintype.sum_bool]; dsimp [χ]; rw [Finset.sum_add_distrib,mul_add,mul_sum,mul_sum]
    have hv1 i : tilt uu i= ∑ j, fee j * flag j i := by
        suffices h : uu i=∑ j,fee j*idx (χ j) i by
            unfold flag; dsimp [tilt]; split_ifs; next => unfold tariff; dsimp only; rw [h, sum_mul,sum_mul]; apply Finset.sum_congr rfl; intros; ring
            simp
        unfold uu; rw [Thermal.cash,hg fun i'=>idx i' i]; simp [idx,nodes]

    change SumBudget (fun i=> tilt uu i) _
    rw [show (fun i=> tilt uu i) = _ from funext hv1]
    apply budget_loosen hv
    rw [hg fun _=>b,sum_const,card_univ,nsmul_eq_mul,Fintype.card_fin]; push_cast; ring_nf; exact le_rfl
def magnify (n : ℕ) := 1+(Thermal.speed n)^n * ((2*(n+1):ℕ):ℝ)
local notation "bF" => (betaF G x L)

def strengthened (Q : Target G P) D C (n:ℕ) := Buy.quote G L μ (1/2) Q.exp Q.ε Q.δ (bF/2) x C 0 (D*Delay.bill G L x^5) (magnify n * Q.goal L x)

lemma enlarged_buy (Q : Target G P) {L:Side} (d:ℕ) {hv : 0<μ} (he:0≤D) (hk:0≤C) : ∀ᶠ x in atTop,(strengthened Q D C d (L:=L) (μ:=μ) (x:=x)).Buy L Q.halo (radiusB x)  := by
  have hz := Buy.quoted G L (u:=1/2) hv (by norm_num) Q.pos Q.bound Q.usable (add_nonneg he hk) (z:=0) (by norm_num) 5 Q.halo
  have hD y := Delay.bill_ge G L y
  let c x:= Animals.ballCost (radiusB x); let B (x:ℝ) := (16*magnify d)*(c x:ℝ)
  have hB : Rate G L 0 B := by
       exact (((Census.width_rate G L 1 0).mul_left (16*magnify d)).congr (Eventually.of_forall fun x=> by simp [c,B]))
  have hP : Rate G L (Q.rate + 0) (fun x=> Q.goal L x * B x) := by exact (Rate.power (a:=Q.rate)).mul hB
  filter_upwards [hz,hP.below (by simpa using Q.stop) Q.δ Q.pos] with x hx hW
  let fee:ℝ := (D+C)*Delay.bill G L x^5
  have ht := hD x; have he' : fee ≥ D+C := le_mul_of_one_le_right (add_nonneg he hk) (one_le_pow₀ ht)
  have hw : D*Delay.bill G L x^5 ≤ fee := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hk) (pow_nonneg (zero_le_one.trans ht) _)
  have hp:0<c x:= (Nat.zero_lt_one.trans_le (Animals.neighbors_ge _))
  have hp':(0:ℝ)<c x:=by exact_mod_cast hp
  -- explicit powers; log coefficients
  let g:=magnify d * Q.goal L x
  apply hx.2 (betaF G x L/2) C 0 (D*Delay.bill G L x^5) g (by exact _root_.le_of_eq (by ring)) le_rfl hk
  · rw [Real.rpow_zero,mul_one]; exact (by calc C ≤ fee := by linarith
                                                 _ ≤ Real.exp fee := (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _))
  · rwa [mul_zero,add_zero,Real.rpow_zero,mul_one]
  · unfold g Target.goal magnify speed; have hQ := hx.1; positivity
    -- last inequality may treat β goal
  unfold Buy.tolerance; refine (le_div_iff₀ (by positivity)).mpr ?_
  exact (le_trans (le_abs_self (Q.goal L x*B x)) hW)|>.trans' (α:=ℝ) (le_of_eq (by unfold B c g; ring))

private def Members (R' : Rep G f)(x : ℝ) := Cash u x μ L Q o C T R'

local notation "blocks" => Fin (n+1)
section
variable {V : Set ℝ} (H : ∀ t∈V,Cash u x μ L Q o C T (scaled R t)) (Ξ : (t:ℝ)→(e:t∈V)→ Utopia (H t e) n v D r C' χ) (γ : ℝ)
-- choose arbitrary zeros OU of set for unconditional wallets
def fl0 (t:ℝ) : Alphabet c f → ℝ := if he:t∈V then rates (Ξ t he).goalsK (Ξ t he).goalsL ((Ξ t he).M*γ) else fun _=> 0
def t0 (t:ℝ) : Head S → ℝ := if he:t∈V then (Ξ t he).tag else fun _=> 0
def flare i := cash (n:=n) t (δ:=δ) (fun t=> fl0 H Ξ γ t i)
def tags i := cash (n:=n) t (δ:=δ) (fun t=> t0 H Ξ t i)
local notation "flare₀" => flare (t:=t) (n:=n) (δ:=δ) H Ξ γ
local notation "tags₀" => tags (t:=t) (n:=n) (δ:=δ) H Ξ
local notation "V₀" => strengthened Q C' (magnify n) n (μ:=μ) (L:=L) (x:=x)
local notation "V₁" tt => Q.costs L μ (RG.Rep.beta (scaled R tt)) x C'
local notation "V₂" ph hh => (Ξ ph hh)
local notation "r'" => nodes t δ (n:=n)
variable (t₁ :ℝ)(hS:t₁ ∈ V)(hC:0≤γ)(hC' : ∀ t (he:t∈V), γ ≤ (Ξ t he).rad) (hn:∀ i j:Fin (n+1),nodes t δ i j ∈ V)
omit t₁ hS
include hC hC'
lemma fl0_pos i (t:ℝ) : 0≤fl0 H Ξ γ t i := by
  unfold fl0; split
  next he=> rcases i with i|i|i
            · exact ((Ξ t he).uses.nonneg (.inl i))
            · exact ((Ξ t he).uses.nonneg (.inr (.inl i)))
            · exact mul_nonneg (Ξ t he).positive hC
  next=> exact le_rfl
lemma flare_pos i : 0≤flare₀ i := by
   have hh:= fl0_pos H Ξ γ hC hC' i
   unfold flare Thermal.cash; exact add_nonneg (hh _) (mul_nonneg (by unfold speed; positivity) (sum_nonneg fun i _=> add_nonneg (hh _) (hh _)))
private lemma update {t} (ht:t∈V) i : fl0 H Ξ γ t i ≤ (Ξ t ht).flair i := by
 dsimp [fl0]; rw [dif_pos ht]; rcases i with z|z|z
 · exact le_rfl
 · exact le_rfl
 exact mul_le_mul_of_nonneg_left (hC' t ht) (Ξ t ht).positive
include hC' hn t₁ hS
lemma accounts : Mixed.Accounts S Q.halo (radiusB x) V₀ (H t₁ hS).birth flare₀ (lengths T (scaled R t₁)) (steamP S V₀) := by
 let h := H t₁ hS
 have hh i j : gross h.birth (radiusB x) (fl0 H Ξ γ (r' i j)) (ConnectedActivityE6.lengths T (scaled R t₁)) (Mixed.Costs.reservePoly V₀) (Mixed.Costs.head V₀) (Q.goal L x) := by
     let f:= r' i j; have he := hn i j; let h' : Cash u x μ L Q o C T (scaled R f) := H f he
     have hp:= ((Ξ f he).accrues.pays); intro y'
     specialize hp y'
     apply budget_mono hp ?_ ?_
     · intro p; split
       next hh=> unfold tariff; have hf : 0≤fl0 H Ξ γ f p:=fl0_pos H Ξ γ hC hC' p f
                 exact mul_nonneg (mul_nonneg hf (Real.exp_pos _).le) (Real.exp_pos _).le
       next hh=> exact le_rfl
     · intro p
       have hx:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (Account.update H Ξ γ hC hC' he p) (a:=Real.exp (2*Q.ε*ConnectedActivityE6.lengths T (scaled R f) p+(0:Alphabet c _→ℝ) p)) (Real.exp_pos _).le) (a:=Real.exp ((V₀).head*coverNumber (radiusB x) (h.birth p))) (Real.exp_pos _).le
       exact (show ∀ (u:Prop) [Decidable u] {a b : ℝ},a≤b → (if u then a else (0:ℝ)) ≤ (if u then b else 0) by intro u _ a b h; split <;> first | exact h | exact le_rfl) (y'∈ h.birth p) hx
 exact ⟨fun _ _=>⟨mul_nonneg ((show 0≤(magnify n) by unfold magnify speed; positivity)) (Real.exp_pos _).le, le_rfl⟩, flare_pos H Ξ γ hC hC', fun i=> Nat.cast_nonneg _, heat_budget hh⟩
end

end YM.UVExt.EnergyRay.Thermal.Account
namespace YM.UVExt.EnergyRay.Thermal.Account
open Function Lattice RG Pressure Pressure.Stores Pressure.Tube Wilson Finset MeasureTheory Tree
open Filter Set ConnectedActivityE6 Gaussian Coat Pulse Blaze Silica Raw Precision
open Push Push.AbsoluteSums Push.SectorMeasure Push.SectorMeasure.Oriented Reserves Footprint
open scoped Topology Classical BigOperators ContDiff
variable {κ : Type*} {c f L : Side} {ε x b : ℝ}
variable {G:Gauge} {S:StepData c f} {P : Teller G} {T : Tube G S} {R:Rep G f} {F : Forest S.ratio}
variable {Q : ConnectedActivityE6.Target G P} {n : ℕ} {u a η μ D C τ δ v r C' : ℝ}{t : ℂ}{o:Target.Order G u}{χ:Chi}
open Mixed.Costs
variable {V : Set ℝ} (H : ∀ t∈V,Cash u x μ L Q o C T (scaled R t)) (Ξ : (t:ℝ)→(e:t∈V)→ Utopia (H t e) n v D r C' χ) (γ : ℝ)
local notation "flare₀" => flare (t:=t) (n:=n) (δ:=δ) H Ξ γ
local notation "tags₀" => tags (t:=t) (n:=n) (δ:=δ) H Ξ
local notation "V₀" => strengthened Q C' (magnify n) n (μ:=μ) (L:=L) (x:=x)
local notation "V₁" tt => Q.costs L μ (RG.Rep.beta (scaled R tt)) x C'
local notation "V₂" ph hh => (Ξ ph hh)
local notation "r'" => nodes t δ (n:=n)
variable (t₁ :ℝ) (hS:t₁ ∈ V) (hC:0≤γ) (hC' : ∀ s (h:s∈V), γ ≤ (Ξ s h).rad) (hn:∀ i j:Fin (n+1),nodes t δ i j∈V)
def crown := Mixed.costs S Q.halo (radiusB x) (steamP S V₀) (flare (t:=t) (n:=n) (δ:=δ) H Ξ γ)
local notation "crown₀" => crown (t:=t) (n:=n) (δ:=δ) H Ξ γ

lemma cash_mono {f g:ℝ→ℝ} (h : ∀ i,f i ≤ g i) : Thermal.cash t (δ:=δ) (n:=n) f ≤ Thermal.cash t (δ:=δ) (n:=n) g := by unfold Thermal.cash speed; gcongr <;> exact h _
lemma cash_const (v : ℝ) : Thermal.cash t (δ:=δ) (n:=n) (fun _=>v)=magnify n*v :=by unfold Thermal.cash magnify; rw [sum_const,nsmul_eq_mul, card_univ,Fintype.card_fin]; push_cast; ring

variable (hμ:0≤μ)
include hn t₁ hS hC hC' hμ
lemma shares {p} (hp : Packets.connected S Q.halo (radiusB x) p) : tags₀ (Sum.inl p) ≤ crown₀ (Sum.inl p) :=by
   unfold crown tags Mixed.costs; dsimp only [Sum.elim]; rw [if_pos hp]
   let f' := steamP S (strengthened Q C' 1 n (x:=x) (μ:=μ) (L:=L)) p
   have h' (tt:ℝ) : t0 H Ξ tt (Sum.inl p) ≤ f' := by unfold t0; split
                                                     next ht=> unfold Utopia.tag stout; rw [Mixed.costs]; dsimp only [Sum.elim]; rw [if_pos hp]
                                                               unfold f' steamP strengthened; unfold Packets.income
                                                               dsimp only [ConnectedActivityE6.Target.costs,Buy.quote]
                                                               have hT:=((H tt ht).laws.intake.window.1)
                                                               rw [(H tt ht).laws.data.funds.length_eq] at hT
                                                               unfold Push.AbsoluteSums.Grant.credit
                                                               apply mul_le_mul_of_nonneg_left _ zero_le_one
                                                               apply Real.exp_monotone
                                                               gcongr
                                                     next=> change 0 ≤ _; unfold f' steamP Packets.income strengthened Buy.quote; exact mul_nonneg zero_le_one (Real.exp_pos _).le
   exact (cash_mono h').trans_eq (Eq.trans (cash_const _) (by unfold f' steamP Packets.income strengthened; simp only [Buy.quote,one_mul]))

lemma crown_income (p:Molecule S) (ht: ConnectedActivityE6.Matter.troupe T (scaled R t₁) Q.halo (radiusB x) p) :
    (∏ i∈p, tags₀ i)*γ^(blaze p).card ≤ ∏ i∈p,crown₀ i := by
    let A:=flare₀
    have e₀ i : 0≤tags₀ i := by
        unfold tags Thermal.cash; have hh z : 0≤t0 H Ξ z i := by
              unfold t0; split
              next h=> exact (Ξ z h).tagged i
              next=> exact le_rfl
        exact add_nonneg (hh _) (mul_nonneg (pow_nonneg (show (0:ℝ)≤speed n by unfold speed; positivity) n) (sum_nonneg fun _ _=> add_nonneg (hh _) (hh _)))
    have eu : t.re∈V := by simpa [nodes] using hn 0 0
    have h₁ i : tags₀ (Sum.inr (.inl i)) = flare₀ (.inl i) := by
         unfold tags flare cash t0 fl0; dsimp [Utopia.tag,stout,Mixed.costs,Utopia.flair,rates]; simp only [eu, hn, dite_true]
         congr 1
    have h₂ i : tags₀ (Sum.inr (.inr (.inl i))) = flare₀ (.inr (.inl i)) := by
         unfold tags flare cash t0 fl0; dsimp [Utopia.tag,stout,Mixed.costs,Utopia.flair,rates]; simp only [eu, hn, dite_true]
         congr 1
    have h₃ i : tags₀ (Sum.inr (.inr (.inr i))) * γ = flare₀ (.inr (.inr i)) := by
         unfold tags flare cash t0 fl0; dsimp [Utopia.tag,stout,Mixed.costs,Utopia.flair,rates]; simp only [eu, hn, dite_true]
         simp_rw [Sum.elim,add_mul, mul_assoc (speed n^n), sum_mul,add_mul]
    have e1 p' (hp: p'∈ p.toLeft): tags₀ (Sum.inl p') ≤ crown₀ (.inl p'):= shares H Ξ γ t₁ hS hC hC' hn hμ (ht.1.checkpoints p' hp)
    apply le_trans _ (prod_le_prod (f:=fun z=> Sum.elim (fun p'=>tags₀ (Sum.inl p')) (fun i=> A i) z) (fun z _=> by
        rcases z with z|z; · exact e₀ _
        exact flare_pos H Ξ γ hC hC' _) (g:=crown₀) (?_ : ∀ z∈p,_≤_)); swap
    · rintro (i|i) hi
      · exact e1 i (mem_toLeft.mpr hi)
      exact le_rfl
    have hP : (∏ i∈p.toRight,tags₀ (Sum.inr i))*γ^(blaze p).card = ∏ i∈p.toRight,A i := by
        unfold blaze; rw [cumulate, cumulate p.toRight A]; change ((∏ i∈_,_ )*((∏ i∈p.toRight.toRight, tags₀ (.inr (.inr i)))))*_ = _
        rw [cumulate p.toRight.toRight,cumulate p.toRight.toRight (fun i=>A (.inr i))]
        unfold A; simp_rw [h₁,h₂,← h₃]; rw [prod_mul_distrib, Finset.prod_const]; ring
    rw [cumulate p, cumulate p (fun z=> Sum.elim (fun p'=>tags₀ (Sum.inl p')) (fun i=> A i) z), mul_assoc]; exact le_of_eq (congr_arg₂ (· * ·) rfl hP)



open Trees
omit hμ hn t₁ hS hC hC'
variable {ι:Type*} {Y:ι→Support c} {B:ℕ} {w d m:ι→ℝ} (ε a : ℝ)
def inked (w:ι→ℝ) (vol:Finset ι→ℝ) (Y:ι→Support c) (ε:ℝ) (p : Finset ι) := if Ac.Spark Y p then ((∏ i∈p,w i)* Real.exp (ε*vol p)) else 0
lemma receive (hZ:0≤a) (hq:0≤ε)(hw:∀ i, 0≤w i)(hd:∀ i,0≤d i) (hh:∀ i,0≤m i)
    (hp : Ready Y B (tariff w d m ε) (a+2*ε) γ b τ) : Ac.Hit (fun p:Finset ι=>p.biUnion Y) B (inked w (setPrice Y B d) Y ε) a (γ*(1-τ)⁻¹) := by
    intro p; let siz y:ℝ:= coverNumber B (Y y); change SumBudget _ _
    have ht := touch_tail Y B hp p 0
    refine budget_loosen (budget_mono ht ?_ ?_) (le_of_eq (by ring))
    · intro p; let M:=p.biUnion Y; split
      next he=> unfold inked; split
                next h=> exact mul_nonneg (mul_nonneg (prod_nonneg fun i _=> hw i) (Real.exp_pos _).le) (Real.exp_pos _).le
                next h=> rw [zero_mul]
      next h=> exact le_rfl
    intro s; simp only [if_pos (Nat.zero_le _)]; unfold inked Trees.touches; split_ifs with h₁ h₂ h₃
    · dsimp at *; unfold currency tariff setPrice
      simp_rw [prod_mul_distrib,← Real.exp_sum, mul_assoc _ _ (Real.exp _),← Real.exp_add]
      apply mul_le_mul_of_nonneg_left _ (prod_nonneg fun i _=> hw i); apply Real.exp_monotone
      change _ ≤ _
      have hc : a*(coverNumber B (s.biUnion Y):ℝ) ≤ a*∑ i∈s,siz i := mul_le_mul_of_nonneg_left (by
                show _ ≤ ∑ i∈s,siz i; unfold siz; rw [←Nat.cast_sum]; exact Nat.cast_le.mpr (Ac.cover _ _ h₂)) hZ
      have hd' := sum_nonneg (s:=s) (f:=d) fun i (_:i∈s)=> hd i; have hm' := sum_nonneg (s:=s) (f:=m) fun i (_:i∈s)=> hh i
      show ε* ∑ i∈s,(siz i+d i)+_ ≤ (∑ i∈s, (2*ε*d i + m i))+ ∑ i∈s,(a+2*ε)*siz i
      rw [sum_add_distrib,sum_add_distrib,←mul_sum,←mul_sum]; have hh': 0≤∑ i∈s,siz i:=sum_nonneg fun _ _=> Nat.cast_nonneg _
      nlinarith
    all_goals simp_all

include t₁ hS hC hC' hn
lemma financed (hh : (V₀).Buy L Q.halo (radiusB x)) : Ac.Hit (H t₁ hS).unionP (radiusB x) (inked crown₀ (H t₁ hS).shapeW (H t₁ hS).supportP Q.ε) Q.exp ((V₀).rootHit * (1-(V₀).q)⁻¹) := by
 let hE := H t₁ hS
 let d := ConnectedActivityE6.lengths T (scaled R t₁)
 have he := accounts H Ξ γ t₁ hS hC hC' hn; let b:= V₀
 have hh:= Mixed.ready_vertices _ _ _ _ hE.birth _ d _ ((hE.laws.data.funds.length_eq).symm ▸ hh : (V₀).Buy S.patch.L Q.halo (radiusB x)) he
 apply receive _ _ _ Q.bound Q.usable.le _ _ _ hh
 · rintro (i | i)
   · unfold Mixed.costs; simp only [Sum.elim]; split_ifs
     next=> exact (he.packetBound i ‹_›).1
     next=> exact le_rfl
   exact he.holds i
 · rintro (i|i); · exact mul_nonneg (show 0≤Mixed.Costs.extraSeed b from le_rfl) (Nat.cast_nonneg _)
   exact he.extra i
 intro i; unfold Mixed.stamp; exact mul_nonneg ‹(V₀).Buy _ _ _›.marked (Nat.cast_nonneg _)
end YM.UVExt.EnergyRay.Thermal.Account
