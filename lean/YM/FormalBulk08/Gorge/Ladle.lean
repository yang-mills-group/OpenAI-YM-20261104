import YM.FormalBulk08.Gorge.Rub

/-! Elementary distribution charge: summed with a free input and a root. Also projects back summability, needed for signed tensor calculus. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Gorge
open Lava Function Wick
open scoped BigOperators Classical ENNReal
variable {V I J : Type*} {D : Reach V} {σ : ℝ} {r : ℕ}

def Fling (D : Reach V) (σ : ℝ) (f : chain V r → I → ℝ) (C : ℝ) := 0 ≤ C ∧ ∀ i a, (∑' v : pack i a, ∑' j, shine σ (wide D v.val)* ‖f v.val j‖ₑ)≤ ENNReal.ofReal C
lemma Fling.bail {f : chain V r→ I→ℝ} {C : ℝ} (h : Fling D σ f C) : Bail D σ (fun v=>∑' i,f v i) C := by
   refine ⟨h.1,fun i a=> (ENNReal.tsum_le_tsum (fun v=>?_)).trans (h.2 i a)⟩
   unfold glitter; rw [ENNReal.tsum_mul_left]; gcongr; exact enorm_tsum_le_tsum_enorm
lemma Fling.summable {f : chain V r→ I→ℝ} {C : ℝ} (h : Fling D σ f C) (hs : 0≤σ) (i : Fin r) (v : chain V r) : Summable (f v) := by
   refine (tsum_enorm_ne_top_iff_summable_norm.mp (ne_top_of_le_ne_top (b:=ENNReal.ofReal C) ENNReal.ofReal_ne_top ?_)).of_norm -- elaborate binder
   let x : pack i (v i):=⟨v,rfl⟩
   have hh:= (ENNReal.le_tsum (f:=fun w : pack i (v i)=> ∑' j,shine σ (wide D w.val)* ‖f w.val j‖ₑ) x).trans (h.2 i (v i))
   refine le_trans (ENNReal.tsum_le_tsum fun j=> le_mul_of_one_le_left' (shine_plus _ hs (wide D v))) hh
lemma Bail.watch {R : Reach I} {a : I} {i} {T : Tile I r} {C : ℝ} (h : Bail R σ T C) (f : J→pack i a) (e : Injective f) :
   (∑' j,glitter R σ T (f j).val) ≤ ENNReal.ofReal C:= (ENNReal.tsum_comp_le_tsum_of_injective e _).trans (h.2 _ _)

def telescopeTerm (q : V→V→ℝ) (T : Tile V (r+1+1)) (v : chain V r) (a : V×V) := halve (q a.1 a.2)*((r+2:ℕ):ℝ)* ((r+1:ℕ):ℝ) * shed (shed T a.2) a.1 v
lemma toss_stare (q : V→ V→ℝ) (T : Tile V (r+1+1)) (B C : ℝ) (hs : 0≤σ) (hB : 0≤B) (h : Bail D σ T C) (he : ∀ a b, |q a b| ≤ B) :
     Fling D σ (telescopeTerm q T) ((B/2*(r+2)*(r+1))*C) := by
   refine ⟨mul_nonneg (by positivity) h.1,fun i a=>?_⟩
   let f : pack i a × (V × V)→ pack (i.succ.succ) a := fun j=> ⟨Fin.cons j.2.2 (Fin.cons j.2.1 j.1.val),by simp [j.1.property]⟩
   have H := h.watch f (by
      rintro ⟨v,b,c⟩ ⟨w,d,e⟩ hv; have hh:=congr_arg Subtype.val hv
      simp only [f] at hh; simp [Fin.cons_inj] at hh; simp [hh.1,hh.2.1,Subtype.ext hh.2.2]);
   rw [← ENNReal.tsum_prod, ENNReal.ofReal_mul (show 0≤B/2*(r+2)*(r+1) by positivity)]
   refine le_trans ?_ (mul_le_mul_right H _); rw [←ENNReal.tsum_mul_left]; refine ENNReal.tsum_le_tsum fun v=>?_
   let M:= halve (q v.2.1 v.2.2)*((r+2:ℕ):ℝ)*((r+1:ℕ):ℝ)
   have hp : |M|≤ B/2*(r+2)*(r+1) := by
       have e:=he v.2.1 v.2.2; unfold M halve; rw [abs_mul,abs_mul,abs_mul]; rw [abs_of_nonneg (show 0≤((r+2:ℕ):ℝ) by positivity), abs_of_nonneg (show 0≤((r+1:ℕ):ℝ) by positivity),Nat.cast_add]; norm_num; gcongr; linarith
   have hl:wide D v.1.val≤wide D (f v).val := known_wide _ _ _ fun k t=> by simpa [f] using reached D (f v).val k.succ.succ t.succ.succ
   unfold glitter; change shine _ _ * ‖M*T (f v).val‖ₑ ≤ _
   rw [enorm_mul,mul_left_comm (ENNReal.ofReal _)]
   gcongr
   · exact shine_le _ hs hl
   rw [←ofReal_norm]; exact ENNReal.ofReal_le_ofReal hp
lemma Bail.stare {q : V→V→ℝ} {T : Tile V (r+1+1)} {B C : ℝ} (hs : 0≤σ) (hB : 0≤B) (h : Bail D σ T C) (he : ∀ a b, |q a b| ≤ B) :
     Bail D σ (stare q T) ((B/2*(r+2)*(r+1))*C) := (toss_stare _ _ _ _ hs hB h he).bail
end YM.FormalBulk08.Gorge
