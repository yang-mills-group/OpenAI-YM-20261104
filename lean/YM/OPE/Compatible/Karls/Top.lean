import YM.OPE.Compatible.Karls.Forte
/-! # homogeneous crowns, going backwards. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Hark
open Function ContinuousLinearMap
open scoped Topology BigOperators Classical
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{m k i:ℕ}{q:ℝ}(p:E→L[ℝ] E)
local notation "X!"=> E→L[ℝ] E
open Filter Finset
section
omit [NormedSpace ℝ E]
variable {f g:ℕ→ E}{u a:ℝ}(h:Thick u f)(h':Thick u g)
lemma Thick.hex (hn:∃ c,Hex a f c)(hp:0 ≤ a)(ht:a<u): Thick u f:= ⟨⟨a,hp,ht,hn⟩⟩
lemma Thick.extend (h:Thick a f)(hh:a≤u): Thick u f:=by obtain ⟨v,hv,he,hN⟩:=h.Bill; exact Thick.hex hN hv (he.trans_le hh)
include h h'
lemma Thick.add: Thick u (f+g):=by obtain ⟨a,ha,he,C,H⟩:=h.Bill; obtain ⟨b,hb,hx,D,V⟩:=h'.Bill; exact Thick.hex ⟨C+D,(H.warm ha (le_max_left ..)).add (V.warm hb (le_max_right ..))⟩ (ha.trans (le_max_left ..)) (max_lt he hx)
lemma Thick.sub: Thick u (f-g):=by obtain ⟨a,ha,he,C,H⟩:=h.Bill; obtain ⟨b,hb,hx,D,V⟩:=h'.Bill; exact Thick.hex ⟨C+D,(H.warm ha (le_max_left ..)).sub (V.warm hb (le_max_right ..))⟩ (ha.trans (le_max_left ..)) (max_lt he hx)
end
variable {A B C:Type}[NormedAddCommGroup A][NormedSpace ℝ A][NormedAddCommGroup B][NormedSpace ℝ B][NormedAddCommGroup C][NormedSpace ℝ C]
open Quit.PriceZ
lemma InvokeB (p:Dice E)(u v:E):‖p u v‖≤‖p‖*‖u‖*‖v‖:= (ContinuousLinearMap.le_opNorm ..|>.trans (mul_le_mul_of_nonneg_right (p.le_opNorm _) (norm_nonneg _)))
lemma hexU {p:ℕ→ Dice A}{u v:ℕ→ A}{a b c x y z:ℝ}(h:Hex a p x)(hp:Hex b u y)(hv:Hex c v z): Hex (a*b*c) (fun i=> p i (u i) (v i)) (x*y*z):=by intro i; refine (InvokeB ..).trans ((mul_le_mul (mul_le_mul (h i) (hp i) (norm_nonneg _) ( (norm_nonneg (p i)).trans (h i))) (hv i) (norm_nonneg _) (mul_nonneg ((norm_nonneg (p i)).trans (h i)) ((norm_nonneg (u i)).trans (hp i)))).trans_eq ?_); rw [mul_pow,mul_pow];ring
-- Telescoping 
local notation "L!"=> Dice E
lemma FarS (p:ℕ→ℕ→L!)(e:ℕ→ℕ→L!)(L:ℕ→X!)(h:∀ i j,p i (j+1) -pullD (L i) (p (i+1) j) = e i j)(x y:ℕ→E)(hx:∀ i,x (i+1)=L i (x i))(hy:∀ i,y (i+1)=L i (y i)) (a k:ℕ):
     p a k (x a) (y a)=p (a+k) 0 (x (a+k)) (y (a+k)) + ∑ i∈ range k, e (a+i) (k-1-i) (x (a+i)) (y (a+i)):=by induction k generalizing a with
     | zero=>simp
     | succ k ih=>
         have he: p a (k+1) (x a) (y a) - p (a+1) k (x (a+1)) (y (a+1)) = e a k (x a) (y a):=by rw [hx,hy]; exact DFunLike.congr_fun (DFunLike.congr_fun (h a k) _) _
         have hp(i:ℕ): a+(i+1)=a+1+i:=by omega
         rw [eq_add_of_sub_eq he,ih (a+1),hp k, Finset.sum_range_succ'];
         simp only [Nat.add_zero,Nat.add_sub_cancel,Nat.sub_zero]; rw [add_comm ((e a k) (x a) (y a)),add_assoc]; congr! 1; rw [add_left_inj]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [hp i,show k-(i+1)=k-1-i from by omega]
-- much simpler avoid series estimate tail. construct B by convergent series. Then recurrence RHS exactly for x* and E. error terminal due B at n via difference between B and Γn∞? telescope limit sum leftover bounded using `B0` constant? compute tail at n formula B−sum_{l≤n} after applying σ^n equals ∑ e*_l(...?) bound a^n cancels. yes.
end YM.OPE.Hark
