import YM.AllOrder.Burn.Torch
import YM.AllOrder.Burn.Notes
/-!
# One harmless ACH enlargement, for the general old E case of qev

We do not substitute this tilted vacuum into the comparison. It only
supplies a bound on regular-occurrence letters.

Most of the algebra in `Multiply`, `Hold`, `Value` extends
`YM/AllOrder/Burn/{Torch,Grades,Rush,Horns,Widow,Revenue,Officer}.lean`.
We need to price all `E` indices carrying error at a fugacity which need
not be an integral power of grow. If we keep the integer convention we'd
need to round down the allowed activation, which would lose a nontrivial
power in the estimate relative to the residual size. The corresponding
all-order Burn path is very convenient when solving for a particular
absolute power budget, rather than this version paying with the *input*
E-size.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Raw
open Filter Function Lattice RG Pressure Pressure.Stores Tree Wilson Finset MeasureTheory
open Push Push.AbsoluteSums Push.AbsoluteSums.Paths Push.AbsoluteSums.Footprint
open SectorMeasure Presented Oriented
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side}
open PhysicalNext.Repeat.Height YM.AllOrder YM.AllOrder.Burn
/-- Enlargements with a general (per letter) factor. -/
structure Multiplier where
 weight : ℕ→ℝ
 upkeep (i:ℕ):1 ≤ weight i
local notation "γ" => (1:ℝ)
abbrev activist (τ:Multiplier)(R:Rep G f): Rep G f:=
  {R with activities:= { R.activities with E:=fun i=> (τ.weight i) • (R.activities.E i)}}
def Tollable (τ:Multiplier){S:StepData c f}(P:Teller G)(T:Tube G S)(x:ℝ)(R:Rep G f) := Intake P T x (activist τ R)
abbrev creditW (τ:Multiplier)(i: LogLetter c f):ℝ:= Sum.elim τ.weight (fun _=>1) i
set_option quotPrecheck false
variable (τ:Multiplier)
lemma creditW_one (i:LogLetter c f): 1≤ creditW τ i:= by
 cases i with
 | inl i => exact τ.upkeep i
 | inr i => exact le_rfl
theorem maskingW (R:Rep G f)(i:ℕ)(U:Config G f):
    (activist τ R).activities.regularOccurrence R.p i U = τ.weight i * R.activities.regularOccurrence R.p i U:= by
 unfold Activities.regularOccurrence; dsimp only; by_cases h:Healthy R.p.threshold (R.activities.reg i).support U; rw [masked_eq _ _ _ _ h,masked_eq _ _ _ _ h]; rfl
 rw [masked_ne _ _ _ _ h,masked_ne _ _ _ _ h,mul_zero]
lemma postsW {S: StepData c f}(x:ℝ)(R:Rep G f)(T:Tube G S)(U:Config G f)(V:Config G c)(i:LogLetter c f):
    expo T x (activist τ R) U V i= creditW τ i * expo T x R U V i := by
 rcases i with j|j|j|j|j|j
 · change -( _ )= τ.weight j *(-_); rw [maskingW]; ring
 all_goals rw [show creditW τ _=1 from rfl,one_mul]; rfl

def altitudeFee (τ:Multiplier) (D:ℝ)(π:ℕ) (i: LogLetter c f):ℝ:= D^gradeA π c f i * creditW τ i
lemma altitudeGE (x:ℝ) (hx:1≤x)(π:ℕ)(i:LogLetter c f):1≤ altitudeFee τ x π i:= one_le_mul_of_one_le_of_one_le (one_le_pow₀ hx) (creditW_one τ i)
-- First-stage absolute weighted price; arbitrary actual configurations.
theorem inherit_multiplier (π:ℕ) (G : Gauge) (P : Teller G) (l : ℕ) {a ε : ℝ} (he : 0<ε) (ha : 0≤a)
    (hx : 4*ε < P.top.supportExponent) (hy : 8*ε < P.top.width) (hz : 8*ε < P.below.width) :
    ∃ n : ℕ, ∀ L : Side, n ≤ L.val → ∀ r : ℝ, -(1/2:ℝ) < r → ∀ r' : ℝ,
      ∀ᶠ x : ℝ in atTop, ∀ (c f : Side) (S : StepData c f) (T : Tube G S) (R : Rep G f), S.patch.L=L →
      Intake P T x R → ∀ (τ:Multiplier), Tollable τ P T x R →
      ∃ z : LogLetter c f → ℝ, (∀ U V i, |expo T x R U V i| ≤ z i) ∧
        Sales (radiusB x) a ε (space T l (radiusB x) R) (fun i=> altitudeFee τ (grow G L x) π i*z i) (extra T R) (betaF G x L ^ r) ∧
      ∃ w : ℕ → ℝ, (∀ i U, |R.activities.K i U| ≤ w i) ∧
        Sales (radiusB x) a ε (forcedFoot S.ratio l (radiusB x) R) w (forcedExtra R) (betaF G x L ^ r') := by
 obtain ⟨n,H⟩:= inherit_deep π G P l he ha hx hy hz; refine ⟨n,fun L hL r hp r'=> ?_⟩; filter_upwards [H L hL r hp r'] with x H c f S T R h hp τ ht
 obtain ⟨p,h',hp,hP⟩:= H _ _ S T _ h ht; let z (i:LogLetter c f):=p i / creditW τ i; have hs i: 0< creditW (c:=c) (f:=f) τ i:= zero_lt_one.trans_le (creditW_one τ i); refine ⟨z,fun U V i=>?_ ,?_, hP⟩
 · unfold z; rw [le_div_iff₀ (hs i)]; conv_lhs=> rw [mul_comm]
   have hf:=h' U V i; rw [postsW,abs_mul,abs_of_pos (hs i)] at hf; exact hf
 have hh(i:LogLetter c f): altitudeFee τ (grow G L x) π i * z i = grow G L x^gradeA π c f i *p i:= by
   have hv:=(hs i).ne'; unfold altitudeFee z; field_simp
 simp_rw [hh]; exact hp
lemma multiplierSales {ι:Type*} {X:ι→Support c} {w:ι→ℝ} {e:ι→ℕ} {a b v : ℝ} {n:ℕ}
    (k : ι→ℝ) (h : Sales n a b X (fun i=> k i*w i) e v) (hp : ∀ i, 1≤k i) : Sales n a b X w e v := by
  have he i:0≤w i:= nonneg_of_mul_nonneg_right (h.nonneg i) (zero_lt_one.trans_le (hp i))
  exact (one_mul v) ▸ h.shift zero_le_one he (fun i=> by rw [one_mul]; exact le_mul_of_one_le_left (he i) (hp i))
end YM.ConnectedActivityE6.Raw
