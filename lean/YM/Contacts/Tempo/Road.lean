import Mathlib.Analysis.SpecificLimits.Normed
/-!
  # PL-age on constant smoothing-L chain in a half-line

  polynomial weights, single logarithm time n (can be at variable length from the
  continuum-LPT measuring point, **not** all-real spacings).
-/
namespace YM.Contacts.Tempo
open Set Filter Finset
open scoped Topology Classical BigOperators NNReal
noncomputable section
variable {n m k j l d:ℕ}{b c:ℝ}
abbrev gap (m n:ℕ):ℝ:= dist (m:ℝ) (n:ℝ)
abbrev toll (m n d:ℕ): ℝ:= (1+gap m n)^d
lemma gap_nn (m n) : 0≤ gap m n:= dist_nonneg
lemma gap_sym (m n): gap m n=gap n m:= dist_comm ..
lemma gap_tri (m n k): gap m n ≤ gap m k+gap k n:= dist_triangle ..
lemma gap_add (n m:ℕ): gap n (n+m)=(m:ℝ):= by simp [gap,dist_comm (n:ℝ)]
lemma toll_good (m n d:ℕ):1≤toll m n d:= one_le_pow₀ (le_add_of_nonneg_right dist_nonneg)
lemma toll_glow (m n d:ℕ):0<toll m n d:= lt_of_lt_of_le zero_lt_one (toll_good ..)
lemma toll_id (m d:ℕ):toll m m d=1:= by simp [toll,gap]
lemma toll_sym (m n d:ℕ):toll m n d=toll n m d:= by simp only [toll,gap_sym n m]
lemma toll_tri (m n k d:ℕ):toll m n d≤ toll m k d*toll k n d:= by unfold toll; rw [←mul_pow]; apply pow_le_pow_left₀ (by exact add_nonneg zero_le_one dist_nonneg); nlinarith only [gap_tri m n k,mul_nonneg (gap_nn m k) (gap_nn k n)]
lemma toll_add (m n d:ℕ):toll n (n+m) d=toll 0 m d:= by unfold toll; rw [gap_add,show gap 0 m=(m:ℝ) from by simpa using gap_add 0 m]
lemma toll_day (m d:ℕ):toll 0 m d=(1+(m:ℝ))^d:= by unfold toll; rw [show gap 0 m=(m:ℝ) from by simpa using gap_add 0 m]
lemma toll_long (m n :ℕ) (h:d≤ k): toll m n d≤ toll m n k:= pow_le_pow_right₀ (le_add_of_nonneg_right dist_nonneg) h
lemma toll_plus (m n d k:ℕ): toll m n d*toll m n k=toll m n (d+k):=(pow_add ..).symm
-- reuse summable results
lemma series_toll (d:ℕ){c:ℝ} (hc:0 < c)(ht:c<1):Summable (fun i:ℕ=>toll 0 i d*c^i):= by
   let f(i:ℕ):=(i:ℝ)^d*c^i; have hf:Summable f:=summable_pow_mul_geometric_of_norm_lt_one d (Real.norm_of_nonneg hc.le|>.trans_lt ht); refine ((summable_nat_add_iff 1).mpr hf).mul_right c⁻¹ |>.congr ?_; intro i; unfold f; rw [pow_succ,toll_day]; push_cast; field_simp; ring
variable {κ ι X: Type}{m':κ→ℕ}{P Q:κ→ℕ→ℝ→Prop}
def Road (v:κ→ℕ)(P:κ→ℕ→ℝ→Prop): Prop:= ∃ d:ℕ,∃ b≥(0:ℝ), ∀ p n,P p n (b*toll (v p) n d)
local notation "π" => Road m'
def Rising (P:κ→ℕ→ℝ→Prop): Prop := ∀ x i (b c:ℝ), b ≤ c → P x i b→ P x i c
lemma Road.by_zero (h:Rising P)(hx:∀ x i,P x i 0) : π P:= ⟨0,0,le_rfl,fun _ _=>h _ _ _ _ (zero_mul ..|>.ge) (hx ..)⟩
lemma Road.by_const (h:Rising P)(hx:∀ x i,P x i b)(hb:0≤b):π P:= ⟨0,b,hb,fun _ _=>h _ _ _ _ (le_mul_of_one_le_right hb (toll_good ..)) (hx ..)⟩
lemma Road.fall (h:π P)(hy:∀ x i b,0≤b→P x i b→Q x i b):π Q:= by obtain ⟨d,b,hb,H⟩:=h; exact ⟨d,b,hb,fun _ _=> hy _ _ _ (mul_nonneg hb (toll_glow ..).le) (H ..)⟩
lemma Road.up (h:π P)(hx:∀ x i b, 0≤b→P x i b→Q x i (c*b))(hc:0≤c):π Q:= by obtain ⟨d,b,hb,H⟩:=h; exact ⟨d,c*b,mul_nonneg hc hb,fun p n=> (mul_assoc c b (toll (m' p) n d)).symm ▸ hx _ _ _ (mul_nonneg hb (toll_glow ..).le) (H ..)⟩
lemma Road.joint (h:π P)(ht:π Q)(H:Rising P)(U:Rising Q):π (fun p i b=> P p i b∧Q p i b):= by
   obtain ⟨d,b,hb,V⟩:=h; obtain ⟨g,c,hc,Z⟩:=ht; let n:= d+g; refine ⟨n,b+c, add_nonneg hb hc,fun p i=>?_⟩; let C:= toll (m' p) i n; have hC:0 ≤ C:= (toll_glow ..).le; constructor; exact H p i _ _ (mul_le_mul (le_add_of_nonneg_right hc) (toll_long _ _ (Nat.le_add_right d g)) (toll_glow ..).le (add_nonneg hb hc)) (V ..); exact U p i _ _ (mul_le_mul (le_add_of_nonneg_left hb) (toll_long _ _ (Nat.le_add_left g d)) (toll_glow ..).le (add_nonneg hb hc)) (Z ..)
lemma Road.many {Y:ι→κ→ℕ→ℝ→Prop} (W:Finset ι) (h:∀ z∈W,π (Y z))(hy:∀ z∈W,Rising (Y z)) :π (fun p i b=> ∀ z∈W, Y z p i b):= by
   induction W using Finset.induction with
   |empty=>exact ⟨0,0,le_rfl,fun p i b h=> (Finset.notMem_empty _ h).elim⟩ -- d metavariable
   |insert z v hz ih=>
     have hb (p) (hp:p∈v):= mem_insert_of_mem (b:=z) hp
     exact ((h z (mem_insert_self ..)).joint (ih (fun i hi=>h i (hb i hi)) (fun i hi=>hy i (hb i hi))) (hy z (mem_insert_self ..)) (fun _ _ _ _ h H i hi=> hy i (hb i hi) _ _ _ _ h (H i hi))).fall (fun _ _ _ _ H i hi=> by rcases mem_insert.mp hi with hz|hz; subst i; exact H.1; exact H.2 i hz)
variable {f g :κ→ℕ→X} [NormedAddCommGroup X]
def Rates (m':κ→ℕ) (f:κ→ℕ→X):Prop:= Road m' (fun p i b=> ‖f p i‖≤ b)
namespace Rates
local notation "ρ" => Rates m'
lemma constant {b:ℝ} (h:0≤b) (he:∀ x i,‖f x i‖≤b):ρ f:= Road.by_const (hx:=he) (fun _ _ _ _ h H=>H.trans h) h
lemma zero : Rates m' (fun _ _=> (0:X)):= constant (b:=0) le_rfl (fun _ _=> (norm_zero).le)
lemma neg (h:ρ f):ρ (fun x i=>-f x i):= Road.fall h (fun _ _ _ _ h=> by change ‖- _‖≤_; rwa [norm_neg])
lemma add (h:ρ f)(he:ρ g):ρ (fun x i=>f x i+g x i):= by
   apply Road.up (Road.joint h he (fun _ _ _ _ h H=>H.trans h) (fun _ _ _ _ h H=>H.trans h)) (c:=2) _ (by norm_num)
   intro x i b hb ht; exact (norm_add_le ..).trans ((add_le_add ht.1 ht.2).trans_eq (two_mul b).symm)
lemma sub (h:ρ f)(he:ρ g):ρ (fun x i=>f x i-g x i):= by simpa only [sub_eq_add_neg] using h.add he.neg
lemma sum (W:Finset ι){Y:ι→κ→ℕ→X}(h:∀ z∈W,ρ (Y z)):ρ (fun x i=>∑ z∈W,Y z x i):= by
   induction W using Finset.induction with
   | empty=>simpa only [Finset.sum_empty] using (@Rates.zero κ X m' _) -- wrong binders
   | insert i z hi ih=> simp_rw [Finset.sum_insert hi]; exact (h i (mem_insert_self ..)).add (ih (fun _ hg=>h _ (mem_insert_of_mem hg)))
lemma mul {f g:κ→ℕ→ℝ}(h:ρ f)(hu:ρ g):ρ (fun x i=> f x i*g x i):= by obtain ⟨d,b,hb,H⟩:=h; obtain ⟨w,c,hc,U⟩:= hu; refine ⟨d+w,b*c,mul_nonneg hb hc,fun x i=> ?_⟩; change ‖f x i*g x i‖≤_; rw [norm_mul,←toll_plus]; exact (mul_le_mul (H x i) (U x i) (norm_nonneg _) (mul_nonneg hb (toll_glow ..).le)).trans_eq (by ring)
-- shifts measured from original reference
lemma along (h:ρ f)(j:ℕ):ρ (fun x i=> f x (i+j)):= by obtain ⟨d,b,hb,H⟩:=h; refine ⟨d,b*toll 0 j d,mul_nonneg hb (toll_glow ..).le,fun x i=> (H x _).trans ?_⟩; apply (mul_le_mul_of_nonneg_left (toll_tri _ _ i d) hb).trans_eq ?_; rw [toll_add j i]; ring
end Rates
end
end YM.Contacts.Tempo
