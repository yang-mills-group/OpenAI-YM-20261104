import YM.Contacts.Loom.Post
/-! Arbitrary point/seam evaluation markets. Clock after.Stage.Star. Uniformly weighted relative spaces.
 A Motion r charges scale‐normalized `cap` using actual n.Point Metrics. -/
namespace YM.Contacts.Loom
open Function Filter Set Finset Metric
open Lattice RG Wilson PhysicalNext.Repeat Pressure ConnectedActivityE6 Blaze
open MeasureTheory Meter
open scoped Topology InnerProductSpace NNReal BigOperators ContDiff Matrix.Norms.Frobenius Interval Classical
set_option linter.unusedVariables false
noncomputable section
variable {E F V Y α γ:ℕ→Type} [∀ i,NormedAddCommGroup (E i)] [∀ i,NormedSpace ℝ (E i)] [∀ i,NormedAddCommGroup (F i)] [∀ i,NormedSpace ℝ (F i)] [∀ i,NormedAddCommGroup (V i)][∀ i,NormedSpace ℝ (V i)] [∀ i,NormedAddCommGroup (Y i)][∀ i,NormedSpace ℝ (Y i)]
variable {N:Meter}{p q r s Z:ℝ}{k j l:ℕ}{f:ℕ→ℝ}
namespace Capture
open PertExtension.Series Radial Milling
variable {X: Mint E α}{T:ℕ→ Mint E α}{x: Frame α E} {a b g:ℕ→ℝ}{h n:ℕ}
lemma Word.limit (w:Word N x k n p X T)(hp:p≤q)(hh:q<0): Word N x k n q X T := ⟨hh,fun i hi=> (w.entries _ hi).lo (mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg _)) le_rfl,w.grade.lo (mul_le_mul_of_nonneg_right hp (by positivity)) le_rfl⟩
lemma Word.replace {Y: Mint E α}(w:Word N x k n p X T) (h:Budget N x k (p*(n+1)) (Y-X)): Word N x k n p Y T:= ⟨w.quiet,w.entries,Arms.cheaper (by abel) (Arms.sum h w.grade)⟩
section exp
-- step width p; degrade radius to q. tame to all k.
lemma electric (q:ℝ)(hq:q<0)(k:ℕ): Root N (F:=fun _=>ℝ) (fun _=>Real.exp) k 0 (N.pow q) := by
    obtain ⟨C,hC,H⟩:= Brush.compact (f:=Real.exp) (k:=k) (isCompact_closedBall (0:ℝ) 1) (fun i _=>Real.contDiff_exp.contDiffAt); exact ⟨⟨fun _=> C, Rush.settle C, (Pouch.small Pouch.canon hq).mono fun i hi=> ⟨hC.le,fun j=>H j.val (mem_closedBall_zero_iff.mpr ((mem_ball_zero_iff.mp j.property).le.trans hi))⟩⟩,Eventually.of_forall fun i=> Real.contDiff_exp.contDiffAt.analyticAt⟩ -- namespace. stat
lemma estimate (ht: Budget N x k p X)(he:p<q)(hq:q<0): Budget N x k (q*(n+1)) (fun i j=> Real.exp ∘ X i j - skel Real.exp (n+1) ∘ X i j):= by
    let e:=electric (N:=N) q hq (max (n+1) k); let b:=Pouch.canon (N:=N) (p:=q); have hf:= Root.reminder e b (le_max_left (n+1) k) hq ; rw [zero_add,Nat.cast_add,Nat.cast_one] at hf; apply Root.application (S:=fun _=>(Real.exp - skel Real.exp (n+1))) (Arms.lo hf le_rfl (le_max_right ..)) (b.bank ht he) b ht he.le
lemma jet_exp (j:ℕ)(x:ℝ) : jet Real.exp j x=(j.factorial:ℝ)⁻¹*x^j:= by
   rw [homogeneous_derivative _ _ _ Real.contDiff_exp.contDiffAt]; apply congr_arg; simp_rw [smul_eq_mul,mul_comm _ x]; rw [iteratedDeriv_exp_const_mul]; simp
def expn (X:Mint E α): Mint E α := fun i j=> Real.exp ∘ X i j
def rol (T:ℕ→ Mint E α)(n:ℕ) : ℕ→Mint E α:= ∑ i∈Finset.range (n+1), (i.factorial:ℝ)⁻¹ • stair T i
lemma Word.active (w:Word N x k n p X T) (hz:T 0=0) (hp:p<q)(hq:q<0): Word N x k n q (expn X) (rol T n):= by
   refine Word.replace (Word.join _ _ _ hq (fun i _=> ((w.powers i).scale (i.factorial:ℝ)⁻¹).limit hp.le hq)) ?_; -- rol unfold
   have ht:= estimate (n:=n) (w.plush hz) hp hq; refine Arms.cheaper ?_ ht; funext i j x; simp [expn,skel,Finset.sum_apply,jet_exp]
-- identify functions scaled by coefficient-series q.P.*
def codes (T : Lamp F)(g:ℕ→ℝ)(u:Shelf E α F)(e:ℕ):Mint E α:= fun i j x=> (g i)^e*layers (T i) e ((g i)⁻¹ • u i j x)
variable [∀ i,FiniteDimensional ℝ (F i)]
lemma codes_omit (T:Lamp F)(g:ℕ→ℝ)(u:Shelf E α F): codes T g u 0=0:= by funext i j x; rw [codes]; rw [Radial.Stationary.layers_zero,mul_zero]; rfl -- name
lemma costSum (T:Lamp F)(g:ℕ→ℝ)(u:Shelf E α F)(s e:ℕ): (rol (codes T g u) s) e = (fun i j t=> (g i)^e * expsum (layers (T i)) s e ((g i)⁻¹ • u i j t)):= by
    funext i j t; set F:= layers (T i); let v:=(g i)⁻¹ • u i j t; let G:=codes T g u; have hh (s l): stair G s l i j t= (g i)^l*Zone.TaylorPow F s l v:= by
       induction s generalizing l with
       | zero=> by_cases h:l=0 <;> simp [stair, h,Zone.TaylorPow] -- finite class Need case 0^0
       | succ s ih=> rw [stair, Zone.TaylorPow, Zone.mul]; unfold branch; simp only [Finset.sum_apply,Finset.mul_sum]; apply sum_congr rfl; intro k hk; change stair G s k.1 i j t * _ = _; rw [ih,show g i ^ l = _ from (by rw [←pow_add,HasAntidiagonal.mem_antidiagonal.mp hk] : g i ^ l = g i^k.1*g i^k.2)]; change _*( (g i)^k.2 * (F k.2 v))=_; ring
    unfold rol expsum; simp only [Finset.sum_apply,Finset.mul_sum]; apply sum_congr rfl; intro l _; change (l.factorial:ℝ)⁻¹* (stair G l e i j t)= _; rw [hh]; change _= _*( _ * Zone.TaylorPow F l e v); ring
end exp
end Capture
end
end YM.Contacts.Loom
