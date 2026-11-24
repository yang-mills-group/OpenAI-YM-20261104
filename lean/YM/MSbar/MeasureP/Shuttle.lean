import YM.MSbar.MeasureP.Dusk
/-! L^4 volume pre-count anchored weights each coordinate.Yarn tests. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Measuring
open Set Function Filter Lattice Whisk
open scoped Topology BigOperators
variable {α β γ:Type}[Fintype α][Fintype β]
open scoped Classical
lemma bead_join(f g:α→β→ℝ)(x:List α)(y:List β): beads f x y*|beads g x y|=beads (fun i j=>f i j * |g i j|) x y:=by induction x generalizing y with
    | nil=> simp [beads]
    | cons a l ih=> cases y with |nil=>simp [beads]|cons i y=> simp only [beads,abs_mul,←ih]; ring
lemma bolt_bound(f : α→β→ℝ)(h:∀ i j,0≤f i j)(l:List α)(Y:ℝ)(hy:0≤Y)(H:∀ i∈l,(∑ j:β,f i j) ≤ Y) : Yarn l.length (beads f l) ≤ Y^l.length:=by
   induction l with
   | nil=> rw [List.length_nil,Yarn]; simp [beads]
   | cons a l ih=>
      have hx:Yarn l.length (beads f l) ≤ Y^l.length:= ih fun i hi=> H i (List.mem_cons_of_mem _ hi)
      have he:= H a (List.mem_cons_self ..)
      simp only [List.length_cons,twilled, beads,pow_succ, sheen]; apply le_trans (Finset.sum_le_sum fun j _=> mul_le_mul_of_nonneg_left hx (h a j)) ?_; rw [← Finset.sum_mul, mul_comm]; exact mul_le_mul_of_nonneg_left he (by positivity)
section
variable {c n:Side}(g:Ratio c n) (f:α→Site n)(v:β→Site c)
noncomputable def swipe (a:ℝ)(p:ℕ)(k:List α):= Whisk.spread f ∅ a p k
-- input magnitude.M general contribution size.Deg.
local notation "L"=>(g.count.val:ℝ)
noncomputable def bonus(a:ℝ)(p:ℕ) (x : α)(w:β):= factor a p (2*separation (f x) (g.embed (v w))/L)
variable {a b Y Z:ℝ}{p m:ℕ}(X:α→β→ℝ) (ha:0≤a) (hb:a/(g.count.val:ℝ) ≤ b) (hy:0≤Y)
local notation "Ψ"=>bonus g f v a p
local notation "π"=>swipe v a p
lemma bonus_pos(a:ℝ)(p:ℕ)(x:α)(w:β):0 < bonus g f v a p x w:=by unfold bonus factor; positivity
variable (hs:∀ i:α,(∑ j:β,bonus g f v a p i j*|X i j|) ≤ Y) (hc:∀ j:β,(∑ i:α,bonus g f v a p i j*|X i j|) ≤ Z)
include ha hy hs
lemma hold (x:α)(y:β)(l:List α){C:ℝ}(hx:factor a p ((extent (Whisk.zone f ∅ (x::l)):ℝ)/L) ≤ C) : Yarn l.length (fun z:List β=>swipe v a p (y::z)*|beads X (x::l) (y::z)|) ≤ C*(bonus g f v a p x y * |X x y|)*Y^l.length:=by
    let F(i)(j) := Ψ i j*|X i j|; have he(i j):0≤ F i j:= mul_nonneg (bonus_pos ..|>.le) (abs_nonneg _); let U:=C*F x y
    have hC :0 ≤ C:= (show _ ≤ factor _ _ _ from by unfold factor; positivity).trans hx; have hu:0≤U:=mul_nonneg hC (he ..)
    apply le_trans (b:=Yarn l.length (fun z:List β=> U*beads F l z)) (shiny l.length ?_) ?_
    · intro r hr; refine (mul_le_mul_of_nonneg_right (le_trans (tensile g f v a p ha (x::l) (y::r) (by rw [List.length_cons,hr,List.length_cons])) (mul_le_mul_of_nonneg_right hx (kids Ψ (fun i j=> (bonus_pos ..).le) _ _))) (abs_nonneg _)).trans_eq ?_
      unfold U; change C*beads Ψ (x::l) (y::r)*|beads _ _ _|= _; rw [mul_assoc,bead_join]; change C*(F x y*beads F l r)= _; ring
    rw [sheen]; exact mul_le_mul_of_nonneg_left (bolt_bound _ he _ _ hy (fun i _=>hs i)) hu
omit ha hy hs
include hb
lemma drops (d :ℕ) : factor a p ((d:ℝ)/L) ≤ Whisk.liftW b p d:=by
    have h:= show (d:ℝ)/L ≤ d from div_le_self (by positivity) (by exact_mod_cast g.count.property); unfold factor liftW
    refine mul_le_mul ?_ (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le (by positivity)
    · exact pow_le_pow_left₀ (by positivity) (by linarith only [h]) _
    rw [show a*((d:ℝ)/L)=a/L*d from by ring]; exact mul_le_mul_of_nonneg_right hb (by positivity)
lemma cutdown {d :ℕ}(hd:g.count.val≤d) : factor a p ((d:ℝ)/L) ≤ (2/L)^p*Whisk.liftW b p d:=by
    have hL:0 < L:=by positivity
    have h:(1:ℝ)+d/L ≤ (2/L)*(1+d):=by field_simp; nlinarith only [(show L ≤ d by exact_mod_cast hd),Nat.cast_nonneg (α:=ℝ) d]
    have hx:a*((d:ℝ)/L) ≤ b*d:=by rw [show a*((d:ℝ)/L)=a/L*d from by ring]; exact mul_le_mul_of_nonneg_right hb (by positivity)
    unfold factor liftW; rw [←mul_assoc,←mul_pow]; exact mul_le_mul (pow_le_pow_left₀ (by positivity) h _) (Real.exp_le_exp.mpr hx) (Real.exp_pos _).le (by positivity)
omit hb
noncomputable def shaft(m:ℕ)(z:α→β→ℝ)(E:List α→ℝ)(w:List β):=Yarn m (fun l:List α=> E l*beads z l w)
noncomputable def ter(m:ℕ)(z:α→β→ℝ)(E:List α→ℝ)(w:List β):=Yarn m (fun l:List α=> E l*|beads z l w|)
include ha hb hs hc hy
variable (F:List α→ℝ)(s:ℝ)
lemma preGold (H:∀ l:List α,l.length=m+1→0≤F l)(ht:∀ i:α,Yarn m (fun l:List α=> F (i::l)*swipe f b p (i::l))≤s)(hh:0≤s)(o:β) : Yarn m (fun l:List β=> swipe v a p (o::l)*ter (m+1) X F (o::l)) ≤ s*Z*Y^m:=by
   let K(x) := Ψ x o * |X x o|; let k(x):= K x*Y^m; have hK(x):0 ≤ k x:=by unfold k K; exact mul_nonneg (mul_nonneg (bonus_pos ..|>.le) (abs_nonneg _)) (by positivity)
   let I(T:List α)(Tt:List β):= swipe v a p (o::Tt)*(F T*|beads X T (o::Tt)|); unfold ter
   conv_lhs=> arg 2; ext; rw [←sheen]
   rw [pool,twilled]
   change (∑ i:α,Yarn m fun l:List α=> Yarn m (I (i::l))) ≤ _
   refine le_trans (Finset.sum_le_sum (g:=fun i:α=>k i*s) fun i _=>?_ ) ?_
   · refine le_trans ?_ (mul_le_mul_of_nonneg_left (ht i) (hK i)); rw [←sheen]; apply shiny; intro Tt hl
     unfold I; change Yarn m _ ≤ _; let T:=i::Tt; calc
      _ = Yarn Tt.length (fun l=> F T*(swipe v a p (o::l)*|beads X T (o::l)|)):=by rw [hl]; apply stitch; intro _ _; ring
      _ ≤ F T*(swipe f b p T*K i*Y^Tt.length):=by rw [sheen]; exact mul_le_mul_of_nonneg_left (hold g f v X ha hy hs _ _ _ (drops g hb ..)) (H T (by simp [T,hl]))
      _ = _:=by rw [hl]; unfold T k; ring
   rw [← Finset.sum_mul,show (∑ i:α,k i)=(∑ i:α,K i)*Y^m from (Finset.sum_mul ..).symm]
   exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hc o) (by positivity)) hh).trans_eq (by ring)
end
end YM.MSbar.Measuring
