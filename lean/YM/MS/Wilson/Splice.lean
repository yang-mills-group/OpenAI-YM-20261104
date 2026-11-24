import YM.MS.Wilson.Growth
import YM.MS.Book.Change
/-!
# Effects at one perturbative order

Including Wave cutoff localized. Not imposing gauge conditions on physical comparison.
 Power parameter polynomial supplied from Team. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Native.Wilsonian
open Function Filter Set Finset Plane Koszul Cylinder Lab Book Convolve Program
open Paint Landau Bare Focus Taylor Draft Sew Chart Color Lattice Logarithm Orient
open PowerSeries (coeff)
variable {G: Gauge}{A P I:Type}(x:ℝ){p q:Team}{k:ℕ} (F:T (Dot G Cover))
abbrev Y (p:Team)(x:ℝ):= fieldV (G:=G) p x ∘ (Prod.fst : LightMode G Cover → _)
section stay
variable (h:∀ i,i≤k→ p i=q i)
include h
lemma ebb {j:ℕ}(hj:j≤k): Rem (shift p x) (shift q x) j:= by intro i hi; simp_rw [shift,PowerSeries.coeff_mk,h i (by omega)]
lemma tastes (X:Plan→Polynomial ℝ) : Rem (affirmative (X∘p) x) (affirmative (X∘q) x) k:= by intro i hi; simp [affirmative,h i hi]
lemma yielding (a:Atom Axis): Rem (adap p a x) (adap q a x) k:= by cases a with| mk a b=>cases a <;> cases b <;> first| exact tastes x h Plan.waveA| exact tastes x h Plan.waveC| exact tickets (tastes x h Plan.waveA)| exact tickets (tastes x h Plan.waveC)
lemma receipts (F:Dot G Cover){v:ℕ}(hv:v≤k): train (Y p x) v F=train (Y q x) v F:= by apply Subtype.ext; ext l; rw [train_v,train_v,offer,offer,compositeList (V:=Y p x) (W:= Y q x) (fun i=>yielding x h i.1.1) l v hv]
lemma remember : wobble G p x F k=wobble G q x F k:= by
    simp_rw [wobble,LinearMap.comp_apply,rolls]; refine Finset.sum_congr rfl fun i hi=>?_ ; obtain hh:=mem_antidiagonal.mp hi; rw [sub_alt (ebb x h (show i.2≤k by omega)), show train _ i.1 (substitute (shift q x) F i.2)= train (Y q x) _ _ from receipts (k:=k) x h _ (show i.1≤k by omega)]; -- inspect
end stay

section start
variable (h:∀ i,i<k → p i=q i)(hv:0<k)
include h hv
local notation "c"=> coeff k (shift q x)-coeff k (shift p x)
-- diagonal generator N_n additive
omit h hv in
lemma frame_clock (X:Team)(v:Dot G Cover): train (Y X x) 0 v=v:= Subtype.ext (price_mem X x v)
lemma splice : wobble G q x F k - wobble G p x F k =(c) • F 1 + (train (Y q x) k (F 0) -train (Y p x) k (F 0)) := by
    have hb : Preset (shift p x) (shift q x) k:= fun i hi=> ebb x (k:=i) (fun i h'=> h i (by omega)) (j:=i) (le_refl i) i (le_refl i)
    let U(P:Team)(j:ℕ×ℕ):= train (Y P x) j.1 (substitute (shift P x) F j.2); let V j := U q j-U p j; let W:= antidiagonal k
    simp_rw [wobble,LinearMap.comp_apply,rolls, ← Finset.sum_sub_distrib]; change ∑ i∈W,V i= _
    classical
    have hi : (0,k) ∈ W:= mem_antidiagonal.mpr (by simp); have ht:(k,0)∈W.erase (0,k):= Finset.mem_erase.mpr ⟨(by rintro h; have he:=congr_arg Prod.fst h; dsimp only at he; omega),mem_antidiagonal.mpr (by simp)⟩
    rw [← Finset.add_sum_erase _ V hi,← Finset.add_sum_erase _ V ht, Finset.sum_eq_zero ?_]; swap
    · intro i hx; obtain ⟨hm,hx⟩:= mem_erase.mp hx; obtain ⟨hl,hx⟩:=mem_erase.mp hx; obtain hp:=mem_antidiagonal.mp hx; have hq:i.1<k := lt_of_le_of_ne (by omega) (fun he=> hm (Prod.ext he (by dsimp only; omega))); have hw:i.2<k:= lt_of_le_of_ne (by omega) (fun h=>hl (Prod.ext (by dsimp only; omega) h)); unfold V U; rw [sub_alt (ebb x (k:=i.2) (fun j hj=> h j (by omega)) (le_refl i.2))] -- cannot h passed
      rw [receipts x (k:=i.1) (p:=p) (q:=q) (fun j hj=> h j (by omega)) _ (le_refl i.1), sub_self]
    unfold V U; rw [add_zero]; congr 1; swap; · dsimp only; rw [pay0,pay0]
    dsimp only; rw [frame_clock, frame_clock, only_one F hb (share ..) hv]; abel -- X typo
end start
end YM.MS.Native.Wilsonian
