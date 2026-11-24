import YM.RG17.Apron
import YM.RG17.Wound

/-!
 Actual representation at individual root (keeping Π unnormalized).
 D0 comparison to particular A will use contraction on aggregate
 selected part AFTER costs of reads, per actual stop. These are additive
 *readouts* in full marker sectors, NOT new polys/Gauge Gates for next
 step and NOT cancellation of any raw-packet norms.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Extraction Spec Set Filter Function MeasureTheory Lattice RG Wilson Marker Overlay Extra.Trajectories
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{S:Table C.book}{f:Extraction.Order}

set_option quotPrecheck false
local notation "π" => Wilson.partition G
local notation "ι" => prior G

-- Integral normalizer separately from pointwise vacuum
abbrev keyMass (C:Family G) (N p:ℕ):ℝ:= Wilson.partition G (C.side N p) (C.beta N p)
def boardMass (C:Family G)(N p j:ℕ)(V:Config G (C.side j p)) := (C.path.rep N p j).eval V
variable (h:C.Makes) (N p :ℕ)
include h
lemma boardPos {j:ℕ}(hj:j ≤ N) : ∀ V, 0 < boardMass C N p j V := Extra.Histories.Tour.bright _ h.wilson N p j hj
lemma boardContinuous {j:ℕ}(hj:j≤ N): Continuous (boardMass C N p j):= by
  rw [show boardMass C N p j= Insertions.vacuum C.path N p j ∘ matrixField from (Insertions.vac_eq h.wilson hj).symm]; exact (Insertions.vac_smooth hj).continuous.comp matrixField_cont
lemma boardFull {j:ℕ}(hj:j ≤ N): (∫ V,boardMass C N p j V∂prior G _) = keyMass C N p:=by
  induction hj using Nat.decreasingInduction with
  | self => rw [show boardMass C N p N= bare (C.beta N p) from (h.wilson.starts _ _).2]; rfl
  | of_succ i hi ih=>
       rw [show boardMass C N p i= (C.path.levels.clock.op i p).push (C.path.β N p (i+1)) (boardMass C N p (i+1)) from (h.wilson.steps N p i hi).1]
       exact (StepData.push_integral (C.path.levels.transition_mass ..) _ ((boardContinuous h N p hi).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).trans ih
omit h
variable {N p} {n:ℕ}(v:Fin n→ C.book.Token)(x:Fin n→Site (C.side N p)) {Γ:Census (Fin n)} (s: Γ.Mode)
-- in readout; don't divide by pointwise Λ before integrating this
abbrev pullDimes (v:Fin n→ C.book.Token)(x:Fin n→ Site (C.side N p)){Γ : Census (Fin n)} (s:Γ.Mode)(j:ℕ)(V:Config G (C.side j p)) :ℂ:=
   (Ride.bump (C.S.a j) s (implants v x).load)⁻¹ * (Tagged v x j V).part s
lemma continuousDimes {j:ℕ}(hj:j≤N):Continuous (pullDimes v x s j):= continuous_const.mul (((implants v x).smooth_total s hj).continuous.comp matrixField_cont)
lemma weighDimes {j:ℕ}(hj:j<N) : pullDimes v x s j= (C.path.levels.clock.op j p).push (C.path.β N p (j+1)) (pullDimes v x s (j+1)):=by
   let e(i:ℕ)(V:Config G (C.side i p)):= (Tagged v x i V).part s
   have hi: Integrable (e (j+1)) (prior ..):= (((implants v x).smooth_total s hj).continuous.comp matrixField_cont).integrable_of_hasCompactSupport (by exact HasCompactSupport.of_compactSpace (e (j+1)))
   let g(t:ℝ):=Ride.bump t s (implants v x).load
   let a(i):=g (C.S.a i)
   let L:ℝ:=(C.S.block j).val; let S:=C.path.levels.clock.op j p; let β:=C.path.β N p (j+1)
   have he:a j=g L*a (j+1):=by
      unfold a g Ride.bump; rw [← Finset.prod_mul_distrib]; apply Finset.prod_congr rfl; intro i _; rw [← mul_pow,C.S.a_step]; have hi:L≠0:=by unfold L; exact_mod_cast (C.S.block j).property.ne'
      unfold L at *; push_cast; field_simp
   have hX {t:ℝ}(ht:t≠0):g t≠0:= Finset.prod_ne_zero_iff.mpr fun i _=> pow_ne_zero _ (mod_cast ht)
   have hL : L≠0:=by unfold L; exact_mod_cast (C.S.block j).property.ne'
   change (a j)⁻¹ • e j= S.push β ((a (j+1))⁻¹ • e (j+1))
   rw [StepData.push_smul S _ _ _ hi, show e j= g L • (S.push β (e (j+1))) from pushesTag v x hj s,smul_smul,he,mul_inv]; field_simp [hX hL, hX (C.S.a_pos (j+1)).ne', a]
include h
lemma fullDimes {j:ℕ}(hj:j≤ N): (∫ V,pullDimes v x (Stock.final (Fin n)) j V ∂prior ..)= (keyMass C N p:ℂ)* C.numeric N p v x:=by
   let s:= Stock.final (Fin n)
   rw [show (∫ V,pullDimes v x (Stock.final (Fin n)) j V ∂prior ..)= _ from integral_const_mul (Ride.bump (C.S.a j) s (implants v x).load)⁻¹ (fun V=>(Tagged v x j V).part s)] -- instantiate prior
   rw [terminalValue h v x hj,mul_assoc]; exact inv_mul_cancel_left₀ (a:=Ride.bump (C.S.a j) s (implants v x).load) (Finset.prod_ne_zero_iff.mpr fun i _=> pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (C.S.a_pos j).ne')) _
omit h
lemma clearedDimes {j:ℕ} (V:Config G (C.side j p)) :
     pullDimes v x s j V/(boardMass C N p j V:ℂ)=(Ride.bump (C.S.a j) s (implants v x).load)⁻¹ * ratioLine v x j V s:= by unfold pullDimes ratioLine; rw [mul_div_assoc]; rfl
end YM.RG17
