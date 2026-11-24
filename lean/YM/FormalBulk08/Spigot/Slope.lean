import YM.FormalBulk08.Dawn.Fern
import YM.FormalBulk08.Broc.Illuminate
import YM.FormalBulk08.Spruce.Height

/-! Finances of field, address and path measures in kme.
All preimages for a test profile kept. Root is movable by translation,
here fixed at origin. ∥w∥ Euclidean native norm. Card axis fixed.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Spigot
open Function Filter Lattice RG Laurent Bloch Exterior Wilson
open Reef Lava Gorge Mesa Shore Lotus Orb Wick Series Jets PowerSeries North Cork City Wine Flat Glide Bank Chapel Rift Kemp Dawn MeasureTheory
open Stationary hiding shine Rays
open scoped Topology ENNReal Matrix BigOperators Classical ContDiff
variable {I:Type*}{G:Gauge}{n:Side}{r t u e E D:ℕ}{A B C σ η:ℝ}
def acres (x:chain (Biglot I) r):ℕ:=∑ i,size (x i).1
lemma acres_slot (x:chain (Biglot I) r)(i:Fin r):size (x i).1≤acres x:=Finset.single_le_sum (f:=fun i=>size (x i).1) (fun _ _=>Nat.zero_le _) (Finset.mem_univ _)
lemma acres_barn (x:chain (Biglot I) r)(o:I):acres x≤(r+1)*herb (fame _) (0,o) x:= by
    have hh i:size (x i).1≤herb (fame _) (0,o) x:= by
       have he:= reached (fame _) (Fin.cons (0,o) x) i.succ 0; simpa [fame,capD,herb] using he
    refine (Finset.sum_le_sum (show ∀ (i:Fin r), i∈Finset.univ→_ from fun i _=> hh i)).trans (?_); simp [add_mul]
lemma barn_small (x:chain (Biglot I) r)(o:I):herb (fame _) (0,o) x≤2*acres x:= by
    let y:chain (Biglot I) (r+1):=Fin.cons (0,o) x; let V:=fame I
    have hk (i:Fin (r+1)) : V.d (y i) (0,o)≤acres x:= by
       cases i using Fin.cases
       · rw [show y (0:Fin (r+1))=(0,o) from rfl,V.self]; exact Nat.zero_le _
       next i=> simpa [V,y,fame,capD] using acres_slot x i
    apply known_wide; intro i j; change V.d (y i) (y j)≤_; refine (V.tri (y i) (0,o) (y j)).trans ?_; rw [V.turn (0,o), two_mul]; exact Nat.add_le_add (hk i) (hk j)
lemma harvest [Fintype I] (o:I)(h:0<σ): Summable (fun x:chain (Biglot I) r=>Real.exp (-σ* herb (fame _) (0,o) x)):= by
    let s:ℝ:=r+1; have hs:0<s:=by unfold s; positivity
    have hm:= monsoon (r:=r) (I:=I) (show 0<σ/s by positivity); refine Summable.of_nonneg_of_le (fun i=> (Real.exp_pos _).le) (fun x=>?_) hm
    rw [prod_shine]; apply Real.exp_monotone; let b:= herb (fame _) (0,o) x
    have hx : (acres x:ℝ)≤s*b:= by unfold s b; exact_mod_cast acres_barn x o
    have ht : (σ/s)*(acres x)≤ σ*b:= (mul_le_mul_of_nonneg_left hx (by positivity)).trans_eq (by field_simp)
    change -σ* (b:ℝ)≤ -(σ/s)*(acres x); nlinarith

lemma sum_tier {α:Type*}{f g:α→ℝ}(h:SumBudget g B)(hp:∀ x, 0≤f x)(ht:∀ x, f x ≤ g x): SumBudget f B:= by
    have hx:=Summable.of_nonneg_of_le hp ht h.2.1; exact ⟨hp,hx,(hx.tsum_le_tsum ht h.2.1).trans h.2.2⟩
lemma cut_barn [Fintype I] (o:I)(hs:η<σ):∃ K:ℝ,0≤K ∧ ∀ (f:chain (Biglot I) r→ℝ) (A:ℝ),0≤A→ (∀ x,0≤f x)→(∀ x,f x≤A*Real.exp (-σ*herb (fame _) (0,o) x)) → SumBudget (fun x=>Real.exp (η*herb (fame _) (0,o) x)*f x) (K*A):= by
    let h:=harvest (r:=r) o (sub_pos.mpr hs);refine ⟨∑' (x:chain (Biglot I) r),Real.exp (-(σ-η)*herb (fame _) (0,o) x),tsum_nonneg fun i=>(Real.exp_pos _).le,fun f A hA hp he=>?_⟩
    refine sum_tier ⟨fun i=> mul_nonneg (Real.exp_pos _).le hA,h.mul_right A,le_of_eq (tsum_mul_right ..)⟩ (fun x=> mul_nonneg (Real.exp_pos _).le (hp _)) (fun x=>?_)
    apply (mul_le_mul_of_nonneg_left (he x) (Real.exp_pos _).le).trans_eq;let t:ℝ:=herb (fame _) (0,o) x
    rw [mul_comm A,←mul_assoc,←Real.exp_add]; change Real.exp (η*t+-σ*t)*A= _; congr 2; ring
lemma actual_penn {x:I}{T:Tile (Biglot I) r} (h:SumBudget (fun v => Real.exp (η*herb (fame _) (0,x) v)*‖T v‖) C): Knoxville (fame _) η (0,x) T C:= by
    refine ⟨(tsum_nonneg h.1).trans h.2.2,?_⟩; refine le_trans ?_ (ENNReal.ofReal_le_ofReal h.2.2); rw [ENNReal.ofReal_tsum_of_nonneg h.1 h.2.1];exact ENNReal.tsum_le_tsum (fun i=> by rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ofReal_norm]; rfl)
end YM.FormalBulk08.Spigot
