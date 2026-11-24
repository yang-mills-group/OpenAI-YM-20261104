import YM.FVA2.O.Hue.Colors
/-!
# Real fee series for insertions in the leading field extraction
Works for infinite formal arrays weighted order-by-order. No prescribed bound on all orders together.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Hue
open MS Function Filter Set Finset MS.Latch Job MS.Plane MeasureTheory Real Metric
open Heat LogTime IntervalFamily Koszul Tone Momentum Landau Fiddle Osc Snap Wire Signal
open Flux Book High Detect MS.Color MS.Local.Physical MS.Land Domain Convolve
open Lives O.Ward MS.City MS.Rake Outlook Tune O.Pad
open scoped Topology ContDiff
variable {E F I:Type}{G:Gauge}{B:Deck G}{K:Booked B}{M:MS_Data G K}{P:IntervalFamily I}{η:I→ℝ}{j n k:ℕ}{t b d:ℤ}{H:Glade G I}{X Y:T (Glade G I)}{a:I→ℝ}
-- translation in coupling order
variable [AddCommGroup E][AddCommGroup F]
def hold0 (n:ℕ) (X:T E) : T E:=fun i=> if n≤ i then X (i-n) else 0
@[simp] lemma hold_1 (X:T E)(n:ℕ): hold0 n X n=X 0:= by simp [hold0]
lemma hx_holder (hp:n≤k){X:T E} : hold0 n X k=X (k-n):= if_pos hp
lemma low_hold (hp:k<n){X:T E}: hold0 n X k=0:= if_neg hp.not_ge
lemma holdZ (k:ℕ): hold0 k (0:T E)=0:= by ext; unfold hold0; simp
lemma hold_add (k:ℕ)(X Y:T E) : hold0 k (X+Y)=hold0 k X+hold0 k Y:= by ext i; by_cases he:k≤ i <;> simp [hold0,he]
@[simp] lemma step_s (n m:ℕ){X:T E}: hold0 (n+1) X (m+1)=hold0 n X m:= by simp [hold0]
variable [Module ℂ E][Module ℂ F] {W:T E}{X':T F}
lemma split_h (L:E →ₗ[ℂ] F→ₗ[ℂ] E): pairW L W (hold0 n X')=hold0 n (pairW L W X'):= by
    induction n with
    | zero=> rw [show hold0 0 X'=X' from funext fun x=>(by simp [hold0])]; ext; simp [hold0]
    | succ n ih=> funext k; cases k with
      | zero=> rw [paired,Finset.Nat.antidiagonal_zero,Finset.sum_singleton,show hold0 (n+1) X' ( ((0,0):ℕ×ℕ).2 )=0 from low_hold (by simp),map_zero,low_hold (by omega)]
      | succ k=> rw [paired, Finset.Nat.sum_antidiagonal_succ',step_s,← ih,paired]; simp only [step_s,low_hold ( Nat.succ_pos n ),map_zero,zero_add]
lemma split_Z (L:E→ₗ[ℂ] F): promote L (hold0 n W)=hold0 n (promote L W):= by ext k; by_cases he:n≤k <;>simp [promised,hold0,he]
lemma shift_R : nav M η (hold0 n X)=hold0 n ( nav M η X ):= by unfold nav; rw [LinearMap.add_apply,LinearMap.add_apply,split_h,split_Z,hold_add]
lemma shift_I : helm M η (hold0 n X)= hold0 n (helm M η X):= by unfold helm; rw [LinearMap.add_apply,LinearMap.add_apply,split_h,split_Z,hold_add]
lemma shift_Response (h:Response X M η b): Response ( hold0 n X ) M η b:= by
    refine ⟨ fun k=>?_,fun k=>?_⟩; · by_cases he:n≤k; rw [hx_holder he]; exact h.life _; rw [low_hold (by omega)]; exact Bank.zero
    rw [shift_I]; by_cases he:n≤k; rw [hx_holder he,hx_holder he]; exact h.vital _; rw [low_hold (by omega),low_hold (by omega)]; exact fun _ _ _=> hasDerivAt_const ..
lemma shift_C (h:Certified X M η b): Certified (hold0 n X) M η b:=⟨ shift_Response h.1,by rw [shift_R,h.2,holdZ] ⟩
lemma shift_Q (h:Reps X b P): Reps (hold0 n X) b P:= by intro k; by_cases he:n≤k; rw [hx_holder he]; exact h _; rw [low_hold (by omega)]; exact Reps_zero (P:=P) k
abbrev entrance (a:T ( I→ℝ ))(X:T ( Glade G I )): T ( Glade G I ):= fun i=>∑ j∈Finset.range (i+1), hold0 j (seat (a j) X) i
def hall (a:T ( I→ℝ ))(X:T ( Glade G I ))(n:ℕ):=∑ i∈Finset.range (n+1), hold0 i ( seat (a i) X )
variable {A B': T ( I→ℝ )}
lemma exact_f : entrance (A+B') X=entrance A X+entrance B' X:= by funext i; simp_rw [ entrance,Pi.add_apply,orientR,hold_add,Pi.add_apply,Finset.sum_add_distrib ]
lemma exact_z : entrance (0:T ( I→ℝ )) X=0:= by funext i; simp only [ entrance, Pi.zero_apply, seat0, holdZ, Finset.sum_const_zero ]
lemma hereΛ (hr:j≤n) : hall A X n j= entrance A X j:= by rw [hall, Finset.sum_apply]; refine Eq.symm (Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hr)) (fun i hi ht=>?_)); rw [low_hold (by simp only [Finset.mem_range] at ht; omega)]
def sameΛ (n:ℕ)(X Y:T ( Glade G I )) : Prop:= ∀ i≤n, X i=Y i
lemma pairΛ (L:Signal.Pair ( Glade G I )) (V:T ( Glade G I )) (hr:sameΛ n X Y): sameΛ n (pairW L V X) (pairW L V Y):= by intro i hi; rw [paired,paired]; exact Finset.sum_congr rfl (fun j hj=> by rw [hr j.2 (by have hz:=mem_antidiagonal.mp hj; omega)])
lemma commuteΛ (L:Signal.Pair ( Glade G I ))(U:MH ( Glade G I ))(V:T ( Glade G I ))(hr:sameΛ n X Y): sameΛ n ( (promote U+pairW L V) X ) ( (promote U+pairW L V) Y ):= by intro i hi; rw [LinearMap.add_apply,LinearMap.add_apply,Pi.add_apply,Pi.add_apply,promised,promised,pairΛ L V hr i hi,hr i hi]
lemma entrance_C (X:T ( Glade G I ))(hr: Certified X M η b): Certified ( entrance A X ) M η b:= by
    have hp(n:ℕ):= C_ο (f:=fun i=> hold0 i (seat (A i) X)) ( Finset.range (n+1) ) (fun i _=> shift_C ( C_seat hr )); have hx(n:ℕ) : sameΛ n ( hall A X n ) ( entrance A X ):= fun i h=>hereΛ h; refine ⟨⟨ fun i=> hereΛ (le_refl i) ▸ ?_,?_ ⟩,?_⟩ -- issue
    · exact ((hp i).1.life i)
    · intro n; unfold helm; rw [← (commuteΛ (both G I).X (both G I).P (Lives.gather M η) (hx n) n (le_refl n): helm M η (hall A X n) n=helm M η (entrance A X) n ),← hereΛ (le_refl n) ]; exact (hp n).1.vital n
    funext n; unfold nav; rw [← (commuteΛ (both G I).C (both G I).J (Lives.gather M η) (hx n) n (le_refl n): nav M η (hall A X n) n=nav M η (entrance A X) n ) ]; exact congr_fun (hp n).2 n
lemma volume_C (h: Reps X t P)(hp:∀ i,Profit P.dawn (A i)): Reps ( entrance A X ) t P:= by intro n; rw [← hereΛ (le_refl n)]; exact Reps_sum ( Finset.range (n+1) ) (f:=fun i=>hold0 i ( seat (A i) X )) ( fun i _=> shift_Q ( Reps_profit (hp i) h ) ) n
lemma solo_h (n:ℕ): entrance ( Pi.single n a ) X=hold0 n (seat a X):= by
    funext i; by_cases he:n≤ i; · unfold entrance; rw [ Finset.sum_eq_single n,Pi.single_eq_same]; intro j hj hp; rw [Pi.single_eq_of_ne hp,seat0,holdZ]; rfl; simp; omega
    rw [low_hold (by omega),entrance]; refine Finset.sum_eq_zero fun j hj=>?_ ; rw [Pi.single_eq_of_ne (by obtain hx:= Finset.mem_range.mp hj; omega),seat0,holdZ]; rfl
end YM.FVA2.O.Hue
