import YM.FormalOPE.RG10.Position.Polys
/-! General curvature grade signs in networks. For use in WilsonX stress choices. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Shutters
open Function Maxwell Labels Extraction Filter Finset Extra.FD PertExtension MeasureTheory
  Topology Metric PertExtension.Position PertExtension.Physical PowerSeries Triangle Matrix
open scoped Topology BigOperators ContDiff Classical
variable {I Q :Type*} {S : Type*} [CommRing S]
local notation "ℒ" => PertExtension.Position.insert

abbrev lapse (n:ℕ) : S := (-1:S)^n
lemma lap_twice (n:ℕ) : lapse (S:=S) n*lapse n=1:= by unfold lapse; simp [← mul_pow]
lemma lap_swap (n:ℕ)(x:S) : lapse n * (lapse n * x) =x:= by rw [← mul_assoc,lap_twice,one_mul]
lemma lap_twist {m n:ℕ} (h:¬ Odd (n+m)): lapse (S:=S) n=lapse m:= by
 have he : lapse (S:=S) n*lapse m=1 := (pow_add (-1:S) n m).symm.trans (((Nat.not_odd_iff_even.mp h).neg_pow (1:S)).trans (one_pow _))
 exact (one_mul (lapse (S:=S) m)) ▸ ((show lapse n *(lapse (S:=S) m*lapse m)= _ from by rw [lap_twice, mul_one]).symm.trans (Eq.trans (mul_assoc (lapse n) (lapse m) (lapse m)).symm (congr_arg (fun v:S=> v*lapse m) he))) -- maybe overkill
variable (shape:Q→ℕ)(w:I→ℕ)
abbrev slots (v:Mark I shape) := ∑ i,w (v.2 i)
def glow (A : Mark I shape→ S) (v:Mark I shape):= lapse (slots shape w v)*A v
def glass (B:FrameAt I S) : FrameAt I S := fun i j=> lapse (w i+w j) * B i j
lemma glow_swap (A : Mark I shape→ S): glow shape w (glow shape w A)= A:= funext fun _=> lap_swap ..
lemma glass_swap (B:FrameAt I S) : glass w (glass w B)=B := funext fun _=> funext fun _=> lap_swap ..
lemma glass_add (B A:FrameAt I S) : glass w (B+A)= glass w B+glass w A := by ext i j; exact mul_add ..
lemma glass_sub (B A:FrameAt I S) : glass w (B-A)= glass w B-glass w A := by ext i j; exact mul_sub ..
def glazed : FrameAt I S→ₗ[S] FrameAt I S where
 toFun:= glass w
 map_add':=glass_add w
 map_smul':= fun i A=> by ext x y; exact mul_left_comm _ _ _
variable [Fintype I]
lemma posed (B:FrameAt I S) (A : Mark I shape→ S) : ℒ I shape (glow shape w A) (glass w B)= glow shape w (ℒ I shape A B):= by
 funext v; let z(v:Mark I shape) := lapse (S:=S) (slots shape w v); let g(u:Fin (shape v.1)→I):=∏ i,B (v.2 i) (u i); unfold glow glass PertExtension.Position.insert; rw [Finset.mul_sum]; apply sum_congr rfl; intro i _; simp_rw [lapse,pow_add,prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
 change ((z ⟨v.1,i⟩)* A _) * (z v* z ⟨v.1,i⟩ *g i)= z v * (A _*g i)
 have he : z ⟨v.1,i⟩*z ⟨v.1,i⟩=1:= lap_twice (slots shape w _); nth_rw 2 [← one_mul (g i)]; rw [← he]; ring

-- sign maps and series
abbrev snooze (A : Mark I shape→fps): Mark I shape→fps:= fun i=> rescale (-1) (glow shape w A i)
abbrev doze (K:FrameAt I fps): FrameAt I fps := fun i j=>rescale (-1) (glass w K i j)
lemma gaze_transition (K:FrameAt I fps)(A: Mark I shape→fps) : ℒ I shape (snooze shape w A) (doze w K)= snooze shape w (ℒ I shape A K) := by funext i; unfold snooze doze; exact Eq.trans (Position.insert_alg (arity:=shape) ((rescale (-1:ℝ))) _ _ _).symm (congr_arg (rescale (-1:ℝ)) (congr_fun (posed shape w K A) i)) -- rescale AlgHom?

private lemma instant (x:fps) (n m) : coeff n (lapse m*x)= lapse m*coeff n x:= by rw [← show C (lapse (S:=ℝ) m)= lapse m by unfold lapse; rw [map_pow,map_neg,map_one], coeff_C_mul]
omit [Fintype I]
lemma ray (K:FrameAt I fps)(n:ℕ) : (fun i j=>coeff n (doze w K i j)) = lapse (S:=ℝ) n • glass w (fun i j=> coeff n (K i j)):= by unfold doze glass; simp_rw [coeff_rescale,instant];rfl
lemma glance (A: Mark I shape→fps) (n:ℕ) : (fun i=>coeff n (snooze shape w A i))= lapse (S:=ℝ) n • glow shape w (fun i=>coeff n (A i)) := by unfold snooze glow; simp_rw [coeff_rescale,instant]; rfl
lemma before (A: Mark I shape→fps) (i v) : coeff i (glow shape w A v)=glow shape w (coeff i ∘ A) v:= instant ..
lemma lamp (A:Mark I shape→fps): (snooze shape w A=A) ↔ (Triangle.parity (slots shape w) A) := by
 have he (v:Mark I shape) : snooze shape w A v=lapse (slots shape w v)*rescale (-1) (A v):= by simp only [snooze,glow,lapse,map_mul,map_pow,map_neg,map_one]
 constructor
 · intro h v; apply Eq.trans (lap_swap _ (rescale (-1) (A v)) |>.symm); rw [← he,h]
 intro h; funext i; rw [he,h]; exact lap_swap ..
end YM.FormalOPE.RG10.Shutters
