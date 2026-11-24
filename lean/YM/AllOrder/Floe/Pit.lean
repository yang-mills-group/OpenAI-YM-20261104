import YM.AllOrder.Floe.Transfer
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Floe
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial
open Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G: Gauge} {c f n : Side} {k j w N : ℕ} {S:StepData c f}
variable {σ C Z D β Θ:ℝ}
namespace StateE
open Bloch Exterior Bid Aero Extra.Iteration Inherited
-- affine-null packet predicate for rank-sum reservoir. sum with tune data entire adherence.
structure Quoted (S: ℕ→Atom G k)(a C:ℝ):Prop where
 pay : Extra.Iteration.Charged S a C
 symm : Extra.Iteration.SymmetricAtoms S
 mute (h:k=2): Silent (h ▸ S)
variable {V F: ℕ→ Atom G k}{a T D:ℝ}
lemma Quoted.pays (h:Quoted V a C) : 0≤ C:= tsum_nonneg h.pay.1|>.trans h.pay.2.2
lemma Quoted.narrow (h:Quoted V a C)(he:σ≤a)(hh:C≤T):Quoted V σ T:= ⟨h.pay.mono he hh,h.symm,h.mute⟩
lemma Quoted.join (h:Quoted V a C)(hf:Quoted F a T): Quoted (Extra.Iteration.join V F) a (C+T):= by
 refine ⟨join_cost h.pay hf.pay,join_sym h.symm hf.symm,fun hk=>?_⟩; subst k; exact join_silent (h.mute rfl) (hf.mute rfl)
section loop
variable (L: Side)
def career (k: ℕ)(L:ℝ)(u v Ω Ω':ℝ) := if k=2 then diffPrice v u Ω Ω'/L^2 else carryPrice v Ω Ω' k/L^(2*k-4)
variable {P Q:Bed}{Ω Ω' w ε η:ℝ}
--
-- Arche `operator dynamic`. repeated α independent Patch.J governor; harmonic only when rank2.
structure Kernel (u v Ω Ω':ℝ)(L:Side)(P Q:Bed)(T:Towers L) : Prop where
 light:u>0
 beam:0<v
 less:v≤u/2*L.val
 high:P.dual_diag.strip v Ω
 low:Q.diagonal.strip v Ω'
 tower:T.Deep v Ω 1
 earlier:Harmonic T
variable {S: Towers L} {u v :ℝ} (h:Kernel u v Ω Ω' L P Q S)
local notation "p'"=> Precision.Towers.Diagonal
-- model chosen before casting L.Ph system. Expedition all ι.Tax.Earn.E and Id.Port.
lemma sustain (G:Gauge) (L:Side) {P Q:Bed} {T:Towers L} (h:Kernel u v Ω Ω' L P Q T) {V:ℕ→Atom G k} (hg:Odd L.val)(hv: Quoted V u C)(hk:2≤k): ∃ X:ℕ→Atom G k, Quoted X v (career k L.val u v Ω Ω'*C) ∧∀ (c f:Side)(W:StepData c f)(hp:W.patch.L=L)(t:Forest W.ratio)(p:Clip)(R:PathData G) ε η, Floor P p f ε η→Bid.Sworn P f G → W.patch.Branches W.kernel G→ Towers.Diagonal W P Q (hp.symm ▸ T) → 0<ε → ∀ ρ,Critical t p R ρ → Guessed t (installed W.ratio (hp.symm ▸ T|>.A0)) ρ → Mentor (ρ:=ρ) (F:=t) V X := by
 obtain he|rfl:= lt_or_eq_of_le hk -- binder order sets k
 · have hZ:v≤u*L.val:= h.less.trans (mul_le_mul_of_nonneg_right (by linarith [h.light]) (Nat.cast_nonneg _)); let Z:= classicalPart P Q T V; refine ⟨Z,⟨?_,classical_sym _ _ _ hv.symm, (fun hp=> False.elim (he.ne hp.symm))⟩,?_⟩; · rw [career,if_neg he.ne']; exact classical_price (le_refl _) h.beam h.high h.low h.tower hv.pay hk hZ
   intro c f W hp t p R ε η hf hm he' hw hF ρ hρ hG; subst L; exact classical_match (le_refl _) h.beam h.high h.low h.tower hF he' hf hm hw hv.pay hk hZ hρ hG k le_rfl
 let Z:= loopPart P Q T V; refine ⟨Z,⟨?_,loop_sym _ _ _ hv.symm,fun _ =>loop_silent (le_refl _) h.beam h.high h.low h.tower hg h.earlier hv.pay h.less⟩,?_⟩ -- placeholders
 · rw [career,if_pos rfl]; exact loop_price (le_refl _) h.beam h.high h.low h.tower hv.pay h.less
 -- revise
 intro c f W hp t p R ε η hf hm he' hw hF ρ hρ hG; subst L; exact loop_match (le_refl _) h.beam h.high h.low h.tower hF he' hf hm hw hv.pay (hv.mute rfl) h.less hρ hG 2 le_rfl
end loop
end StateE
end YM.AllOrder.Floe
