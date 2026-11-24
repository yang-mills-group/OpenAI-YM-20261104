import YM.RGComparison01.Ranch
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Boulevard.Views
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Token.Tune
/-!
# Centred analytic offers, β-weighted Taylor pricing

 Base and lower given data, plus model masks (untested beyond on the
 same sunny hull). Keep full Fréchet jets. Includes all Taylor
 remainder on *model or base* side for analytic probes, not just true
 `aux_push`. RG02 to identify coefficients so produced; do not identify
 ordering after reset. -/

set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open PhysicalNext.Repeat Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open Push.AbsoluteSums Fare Sienna AuxDesk Token AuxFabric AuxConstant AuxMiles AuxWeigh AuxPackage AuxBeam AuxSpell AuxJets AuxStage
open Tensor WilsonStartup
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MatrixOrder
variable {G : Gauge} {c f : Side} {S:StepData c f} {k n j m:ℕ} {C σ v u d Q M H Λ α β : ℝ}
section centred
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace Spline
def centre (f:E→ℝ) (x:E):= f x-f 0
def centred (f:Co E) := fun i : ℕ=>centre (f i)
lemma Field.centred (f : Co E) (h: Spline.Field j n f) : Spline.Field j n (Spline.centred f):= fun i hi=> (h i hi).sub (Spline.vacant _ j)
lemma points_centred {f : Co E} {g : E→ℝ} {x : E} (h : AuxStage.Points d u v n k g x f) (hp : AuxStage.Points d u v n k g 0 f): AuxStage.Points (2*d) u v n k (centre g) x (centred f) := by
  have hx i y : headAt (centred f) v i y=headAt f v i y-headAt f v i 0:= by unfold headAt centred centre; rw [smul_zero]; ring
  let K:=centre g; let v' := AuxStage.price f v n
  have hz y: AuxStage.price (centred f) v n y=v' y-v' 0:= by simp_rw [AuxStage.price,hx,Finset.sum_sub_distrib]; rfl
  constructor
  · intro i hi; rw [funext (hx i)]; refine ((h.bill i hi).separating (AuxCurtain.constant (p:=d*v^i) hp.pos ((hp.bill i hi).bound))).climb (le_of_eq ?_) le_rfl
    ring
  apply ((h.tail.separating (AuxCurtain.constant (p:=d*v^(n+1)) hp.pos hp.tail.bound)).climb (le_of_eq (show d*v^(n+1)+d*v^(n+1) = 2*d*v^(n+1) by ring)) le_rfl).shimmy
  refine Eventually.of_forall fun y=>?_; change (g y-g 0) - AuxStage.price (centred f) v n y=g y-v' y-(g 0-v' 0); rw [hz]; ring
lemma centred_incomes {f:E→ℝ} (hn: 1 ≤ n) (hC:0≤C) (h : ∀ x : E, x∈ball 0 1 → ContDiffAt ℝ (n:WithTop ℕ∞) f x ∧ ∀ i,0 < i → i ≤ n → normJ i f x ≤ C)
    (x : E) (hx: x∈ball 0 1) : Brush n C 1 (centre f) x := by
  let v : E→ℝ:= fun _=> f 0
  have hv : centre f=f-v:= rfl
  rw [hv]; have ht (x) (hx:x∈ ball 0 1): ContDiffAt ℝ (n:WithTop ℕ∞) v x:= contDiffAt_const
  have he := PhysicalNext.Repeat.Shellac.pools (f:=f-v) zero_lt_one (le_refl _) hn hC (le_refl 0) (fun x hx=> (h x hx).1.sub (ht x hx)) ?_ ?_ x hx
  · simpa using he
  · intro i hi hf x hx
    unfold normJ; rw [iteratedFDeriv_sub_apply ((h x hx).1.of_le (Nat.cast_le.mpr hf)) (contDiffAt_const)]; obtain ⟨i,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : i≠0); rw [iteratedFDeriv_succ_const, Pi.zero_apply,sub_zero]; exact (h _ hx).2 i.succ hi hf
  intro i hi; rw [show i=0 by omega,normJ,norm_iteratedFDeriv_zero (𝕜:=ℝ)]; simp [v]
end Spline
end centred

namespace Bonus
open Spline
variable (T:Tube G S)
local notation "Xs" => Positions (Uniform.Primary c G)
local notation "actualᵥ" => (fun x:Xs=>Boulevard.actual x) -- abbrev
local notation "u'" => Uniform.Primary c G

def locus (x:Xs) := mainTerm T.low T.down (actualᵥ x)
def plume (α:ℝ) (x:Xs):=draft α T.down T.low (tint G _ x)
def spine (x:ℝ×Xs):= centre (locus T) x.2
def baseP (α:ℝ):= ritual (spine T) 2 + ritual (fun x:ℝ×Xs=>centre (Bonus.plume T α) x.2) 0
def ember (α β:ℝ) (V:Config G c):= β*mainTerm T.low T.down V+(α*secondTerm T.low T.down V+Precision.loop T.down V)
lemma sunlight (s:Signed) (b:Site c) : locus T ∘ Token.shift s b G=locus T:= funext fun x=> by
  dsimp only [locus, Function.comp_apply]; unfold Boulevard.actual; rw [show represent ((tint G (Exterior.Body 1 c)) ((Token.shift s b G) x))=_ from Token.slip s b x]; exact AnalyticNext.QuarticMatch.Joint.main_pull ..

variable (E:BareRates.pre G σ C k) (he:T.down.Bounds T.low σ C Λ)
    (hM:1≤ M) (hP:(Fintype.card (Uniform.Primary c G):ℝ) ≤ M)
    (hf:n+2 < k)
include he E hM hP hf
lemma into_core (x: ℝ×Xs) (α:ℝ) (hx:x ∈ ball 0 1) :
    let V:= tollS M k (BareRates.bill E T.low); let v:= tollS M k ((1+|α|+Λ)*BareRates.bill E T.low)
    Brush k V 1 (spine T) x ∧ Brush k v 1 (fun x:ℝ×Xs=> Spline.centre (Bonus.plume T α) x.2) x := by
  intro d d'; have ht: 0<BareRates.bill E T.low:= (bareSocket c E he (mem_ball_self (x:=(0:Xs)) zero_lt_one) 0)|>.2.2.2.1
  have hΛ:= hasInheritance he; have h₀ : 0≤d:= by unfold d tollS; positivity
  have h₁ : 0≤d':= by unfold d' tollS; positivity
  have hp₀ y (hy:y∈ball (0:Xs) 1) := bareSocket c E he hy α
  let L:= ContinuousLinearMap.snd ℝ ℝ Xs; have hx' : L x∈ball 0 1 := mem_ball_zero_iff.mpr ((_root_.norm_snd_le x).trans_lt (mem_ball_zero_iff.mp hx)); have he : ‖L‖ ≤ 1 := ContinuousLinearMap.norm_snd_le ..
  constructor
  · apply (Brush.reading L (g:= Spline.centre (locus T)) (Spline.centred_incomes (n:=k) (by omega) h₀ _ _ hx') he).climb le_rfl (by rw [one_mul])
    intro x hx; obtain ⟨hp,_,hr,h',hs,hB⟩:= hp₀ x hx; exact ⟨hp.of_le le_top, fun i hi hh=> ratifyS hM hP hr h'.le hs hh hi⟩
  apply (Brush.reading L (g:=Spline.centre (Bonus.plume T α)) (Spline.centred_incomes (n:=k) (by omega) h₁ _ _ hx') he).climb le_rfl (by rw [one_mul]); intro x hx
  obtain ⟨hp,hp',hr,h',hs,hB⟩:= hp₀ x hx; exact ⟨hp'.of_le le_top,fun i hi hh=> ratifyS hM hP hr (by positivity) hB hh hi⟩

omit hM hP hf in
lemma longarm : FlatAt 2 (spine T) 0:= by
  have hh : DifferentiableAt ℝ (locus T) 0:= (bareSocket c E he (x:=(0:Xs)) (mem_ball_self zero_lt_one) 0).1.differentiableAt (by decide)
  have ht:= Token.crest (Bonus.sunlight T) hh
  let L:= ContinuousLinearMap.snd ℝ ℝ Xs; have he : L 0=0:=map_zero L
  have hx : DifferentiableAt ℝ (locus T) (L 0):= he.symm ▸ hh
  let K : ℝ×Xs→ℝ:= fun _=> locus T 0
  intro i hi; interval_cases i
  · ext1 u; simp [spine,centre]
  ext1 u; rw [iteratedFDeriv_one_apply]; change fderiv ℝ (locus T ∘ L - K) 0 _=0; rw [fderiv_sub (hx.comp 0 L.differentiableAt) (show DifferentiableAt ℝ K 0 from differentiableAt_const _),fderiv_comp _ hx L.differentiableAt, he,ht]; simp [K]

def baseFee {μ C : ℝ} (E : BareRates.pre G μ C k) (p:Clip) (W V A d:ℝ) (n:ℕ) := ritual_fee 2 n (tollS W k (BareRates.bill E p)) 0 d + ritual_fee 0 n (tollS W k ((1+A+V)*BareRates.bill E p)) 0 d
lemma pricing (α:ℝ) (hv:0 < β) (hd:1 < d) (h:d*gStep β ≤ 1) (hn:j≤k) (x:Xs) (hx:‖x‖<d*gStep β):
    AuxStage.Points (baseFee E T.low M Λ |α| d n) ((d*gStep β)⁻¹) (gStep β) n j (Spline.centre (ember T α β ∘ Boulevard.actual)) x (baseP T α):= by
  let y:=gStep β; have ht:=Fare.gS β hv
  let K:=d*y; have hy:0<K:= mul_pos (zero_lt_one.trans hd) ht.1
  let g (x:ℝ×Xs):= centre (Bonus.plume T α) x.2
  have hV (x) (hx:x∈ball (0:ℝ×Xs) K):=Bonus.into_core T E he hM hP hf x α (ball_subset_ball h hx)
  have hz:=hV _ (mem_ball_self hy)
  have hv':y⁻¹^(2:ℕ)=β:= by unfold y; rw [inv_pow]; field_simp [ht.1.ne']; nlinarith only [ht.2]
  have hf₀:= ritual_P (u:=0) hf hn (hz.1.smaller hf.le).smooth (longarm T E he) ht.1 hd h hx (fun x hx=> (hV x hx).1) (by simp only [sub_self,zero_mul]; exact AuxCurtain.constant (u:=0) zero_le_one norm_zero.le)
  have h' : n+0<k:= by omega
  have hg:= ritual_P (f:=g) (u:=0) h' hn (hz.2.smaller h'.le).smooth (show FlatAt 0 g 0 from (fun i hi=> (Nat.not_lt_zero _ hi).elim)) ht.1 hd h hx (fun x hx=> (hV x hx).2) (by rw [show (fun x:ℝ×Xs=>centre (Bonus.plume T α) x.2)=g from rfl,sub_self,zero_mul]; exact AuxCurtain.constant (u:=0) zero_le_one norm_zero.le)
  apply (hf₀.add hg).adjust; refine Eventually.of_forall fun i=>?_
  change β * locus T i+ Bonus.plume T α i-(β*locus T 0+Bonus.plume T α 0) = y⁻¹^2*(locus T i-locus T 0)+ y⁻¹^0*g _; unfold g Spline.centre; rw [hv']; ring
end Bonus
end YM.RGComparison01
