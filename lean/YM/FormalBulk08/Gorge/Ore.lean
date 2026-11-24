import YM.FormalBulk08.Lava.Tide

/-! Absolute kernel strip in own units. Main norm holds FULL root (incl type).
No smearing or gauge quotient taken in this norm. Includes all nonnull field roots.
`Lava.Tile` absolute normalization, not kernel for density. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Gorge
open Lava
open scoped Classical BigOperators ENNReal
variable {V I : Type*}
structure Reach (V : Type*) where
   d : V→V→ℕ
   self : ∀ a,d a a=0
   turn : ∀ a b,d a b=d b a
   tri : ∀ a b c,d a c≤d a b+d b c

variable {r : ℕ} (D : Reach V)
def wide (v : chain V r) := Finset.univ.sup (fun i: Fin r × Fin r=> D.d (v i.1) (v i.2))
lemma reached (v : chain V r) (i j : Fin r) : D.d (v i) (v j) ≤ wide D v := Finset.le_sup (f:=fun a: Fin r×Fin r=>D.d (v a.1) (v a.2)) (Finset.mem_univ (i,j))
lemma known_wide (v : chain V r) (B : ℕ) (h : ∀ i j,D.d (v i) (v j)≤ B) : wide D v ≤ B := Finset.sup_le fun i _=> h i.1 i.2

variable (σ : ℝ)
def shine (n : ℕ) := ENNReal.ofReal (Real.exp (σ*n))
lemma shine_le (h : 0≤σ) {m n : ℕ} (e : m≤n) : shine σ m ≤ shine σ n:= by unfold shine; gcongr
lemma sheen_le {τ : ℝ} (h : τ ≤ σ) (n : ℕ) : shine τ n ≤ shine σ n := by unfold shine; gcongr
lemma shine_one (n) : shine 0 n=1:=by simp [shine]
lemma shine_add (m n) : shine σ (m+n)=shine σ m * shine σ n := by rw [shine,Nat.cast_add,mul_add,Real.exp_add,ENNReal.ofReal_mul (Real.exp_pos _).le]; rfl
lemma shine_plus (h : 0≤σ) (n : ℕ) : 1 ≤ shine σ n := by rw [←shine_one n]; exact sheen_le σ h _

abbrev pack (i : Fin r) (a : V) := {v : chain V r // v i=a}
def glitter (T : Tile V r) (v : chain V r) := shine σ (wide D v)* ‖T v‖ₑ

def Bail (T : Tile V r) (C : ℝ) := 0≤C ∧ ∀ i a,(∑' v : pack i a, glitter D σ T v.val) ≤ ENNReal.ofReal C
lemma bail_void (r : ℕ) : Bail D σ (0 : Tile V r) 0:=⟨le_rfl,fun i a=>by simp [glitter]⟩
variable {D σ}
lemma Bail.mono {T : Tile V r} {C B : ℝ} (h : Bail D σ T C) (hb : C ≤ B) : Bail D σ T B :=⟨h.1.trans hb,fun i a=>(h.2 i a).trans (ENNReal.ofReal_le_ofReal hb)⟩
lemma Bail.shrink {T : Tile V r} {C τ : ℝ} (h : Bail D σ T C) (e : τ ≤ σ) : Bail D τ T C := by
   refine ⟨h.1,fun i a=> le_trans ?_ (h.2 i a)⟩; exact ENNReal.tsum_le_tsum fun v=> mul_le_mul_left (sheen_le _ e _) _
lemma Bail.seen {T : Tile V r} {C : ℝ} (h : Bail D σ T C) (v : chain V r) (i : Fin r) : glitter D σ T v ≤ ENNReal.ofReal C :=
   (ENNReal.le_tsum (f:=fun w:pack i (v i)=>glitter D σ T w.val) (⟨v,rfl⟩ : pack i (v i))).trans (h.2 i _)
lemma Bail.value {T : Tile V r} {C : ℝ} (h : Bail D σ T C) (hs : 0≤σ) (v : chain V r) (i : Fin r) : |T v|≤C := by
   have ht := (h.shrink hs).seen v i; rw [glitter,shine_one,one_mul,←ofReal_norm] at ht; exact (ENNReal.ofReal_le_ofReal_iff h.1).mp ht
lemma Bail.add {T S : Tile V r} {C B : ℝ} (h : Bail D σ T C) (e : Bail D σ S B) : Bail D σ (T+S) (C+B) := by
   refine ⟨add_nonneg h.1 e.1,fun i a=>?_⟩
   rw [ENNReal.ofReal_add h.1 e.1]; refine le_trans ?_ (add_le_add (h.2 i a) (e.2 i a))
   rw [←ENNReal.tsum_add]; refine ENNReal.tsum_le_tsum fun v=> ?_
   unfold glitter; rw [←mul_add]; gcongr; exact enorm_add_le ..
lemma Bail.neg {T : Tile V r} {C : ℝ} (h : Bail D σ T C) : Bail D σ (-T) C:= by refine ⟨h.1,fun i a=> ?_⟩; simpa only [glitter,Pi.neg_apply,enorm_neg] using h.2 i a
lemma Bail.sub {T S : Tile V r} {C B : ℝ} (h : Bail D σ T C) (e : Bail D σ S B) : Bail D σ (T-S) (C+B) := sub_eq_add_neg T S ▸ h.add e.neg
lemma Bail.smul {T : Tile V r} {C : ℝ} (h : Bail D σ T C) (b : ℝ) : Bail D σ (b • T) (|b| * C) := by
   refine ⟨mul_nonneg (abs_nonneg _) h.1,fun i a=>?_⟩
   rw [ENNReal.ofReal_mul (abs_nonneg b)]; refine le_trans ?_ (mul_le_mul_right (h.2 i a) (ENNReal.ofReal |b|))
   rw [←ENNReal.tsum_mul_left]; apply ENNReal.tsum_le_tsum; intro v; apply le_of_eq; unfold glitter; rw [Pi.smul_apply,smul_eq_mul,enorm_mul,←Real.norm_eq_abs b, ofReal_norm,mul_left_comm]
lemma bail_many (S : Finset I) (T : I→ Tile V r) (C : I→ℝ) (h : ∀ i∈S,Bail D σ (T i) (C i)) : Bail D σ (∑ i∈S,T i) (∑ i∈S,C i) := by
   induction S using Finset.induction with
   | empty=> simp only [Finset.sum_empty];apply bail_void
   | @insert a s he ih=> rw [Finset.sum_insert he,Finset.sum_insert he];apply (h _ (Finset.mem_insert_self ..)).add (ih fun i hi=>h i (Finset.mem_insert_of_mem hi))
end YM.FormalBulk08.Gorge
