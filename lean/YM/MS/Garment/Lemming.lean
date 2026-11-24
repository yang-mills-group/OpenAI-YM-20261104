import YM.MS.Garment.Pilasters
/-!
# Angle and spin preservation for continued kernel operations
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Garment.Wick
open Function Set Filter Finset MeasureTheory Real Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps
open Momentum Metric City Color
open scoped Topology ContDiff
open Complex (I)
variable (G:Gauge) (s:ℝ){m n:ℕ}{A C: Type}[Fintype A][DecidableEq A]
lemma mat1 : Ruddy true (A0 G s) where
    turn n X h:= card_tr _ X (realW X (exp s))
    grows h i j p:= by rcases i with ⟨⟨_|i,_|_⟩,a⟩ <;> rcases j with ⟨⟨_|j,_|_⟩,b⟩ <;> first | rfl | (simp [A0,Landau.choir,line,coat,Left, precision,delta,scaling,sq_up,lasts, embA])

def WithinD (F:ℝ→ℝ):Rip G:= fun _=> Landau.choir (laplace (fun p=> F p.sq)) id
lemma mat2 (F:ℝ→ℝ): Ruddy true (WithinD G F) where
    turn n X h:= card_tr _ X (cur_r X F)
    grows h i j p:= by rcases i with ⟨⟨_|i,_|_⟩,a⟩ <;> rcases j with ⟨⟨_|j,_|_⟩,b⟩ <;> first| rfl| simp [WithinD,Landau.choir, laplace,sq_up,Left,embA,delta]
lemma B_shape : B0 G s= WithinD G (fun p=> (1+ (exp s)^2*p)*exp (- ((exp s)^2*p))) := by
    funext m; unfold B0 WithinD; congr! 1; congr! 1; ext; simp [Landau.low,coat,scaling]
lemma L_shape : L0' G s= WithinD G (fun p=> -(2:ℝ)* ((exp s)^2*p)^2 * exp (- ((exp s)^2*p))) := by
    funext m; unfold L0' WithinD; congr! 1; congr! 1; ext; simp [Landau.dotLow,coat,scaling]
lemma genB: Ruddy true (B0 G s):= by rw [B_shape]; apply mat2
lemma genL: Ruddy true (L0' G s):= by rw [L_shape]; apply mat2
-- count, veil
lemma kred : Credit 0 (A0 G s):= by
    intro m i j p hp; contrapose! hp; unfold A0 Landau.choir; split; swap; rfl
    rcases i with ⟨⟨_|i,_|_⟩,a⟩ <;> rcases j with ⟨⟨_|j,_|_⟩,b⟩ <;> norm_num [ghostNo,ghostChannel] at hp <;> rfl
lemma lap_cr (F:ℝ→ℝ): Credit 1 (WithinD G F):= by
    intro m i j p hp; contrapose! hp; unfold WithinD Landau.choir; split; swap; rfl
    rcases i with ⟨⟨_|i,_|_⟩,a⟩ <;> rcases j with ⟨⟨_|j,_|_⟩,b⟩ <;> norm_num [ghostNo,ghostChannel] at hp <;> rfl
lemma voile_a : veil (A0 G s) := by
    intro m i j p; unfold A0 Landau.choir; split; swap; simp
    rcases i with ⟨⟨_|i,_|_⟩,a⟩ <;> rcases j with ⟨⟨_|j,_|_⟩,b⟩ <;> simp [line,coat,← Complex.exp_conj]
lemma voile_W (F:ℝ→ℝ) : veil (WithinD G F):= by
    intro m i j p; unfold WithinD Landau.choir; split; swap; simp
    rcases i with ⟨⟨_|i,_|_⟩,a⟩ <;> rcases j with ⟨⟨_|j,_|_⟩,b⟩ <;> simp [laplace]
end YM.MS.Garment.Wick
