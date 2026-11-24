import YM.MSbar.Whisk.Wall
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Whisk
open Function Filter Finset Cacao
open scoped BigOperators Classical
variable {σ ι A:Type} [Fintype σ]
open Lattice MvPolynomial
local notation "P"=> Pot σ
variable {n:Side}{l : σ→ Site n}{W: Finset (Site n)} {Y Z:Finset (Site n)} {x y z:Site n}{ξ : View σ}
variable {m p q d' :ℕ} {S r a b t u v B D E :ℝ}{f g F F' g' H H' h:Pot σ}{T R: List σ} {k k':σ→σ→ℝ}
-- info unmarked response and phase root. two scales track. choose common t.
structure Gain (l:σ→Site n)(x:Site n)(a B:ℝ)(p:ℕ)(k k':σ→σ→ℝ)(t ε:ℝ) :Prop where
   sober :0≤a
   green :0≤ B
   soft :0≤ε
   full :LoopNet l (a+B) p k t
   group : LoopNet l (a+B) p k' t
   step :Dorian l x a B p (k-k') ε
lemma Gain.flip (g:Gain l x a B p k k' t D):Gain l x a B p (fun i j=> k j i) (fun i j=>k' j i) t D:= ⟨g.sober,g.green,g.soft,g.full.loom,g.group.loom,g.step.flip⟩
structure Paired (l:σ→Site n)(x:Site n)(a B:ℝ)(p m:ℕ)(ξ: View σ)(f g:Pot σ)(t ε E:ℝ):Prop where
    input: Tokew l (a+B) p m ξ f t
    other: Tokew l (a+B) p m ξ g t
    change: Vigor l x a B p m ξ (f-g) (E*ε)
structure Starry (l:σ→Site n)(x:Site n)(a B:ℝ)(p m:ℕ)(ξ: View σ)(f g:Pot σ)(t ε E:ℝ):Prop where
    input : Vault l {x} (a+B) p m ξ f t
    other : Vault l {x} (a+B) p m ξ g t
    change: Vault l {x} a p m ξ (f-g) (E*ε)
variable (H₀:Gain l x a B p k k' b D)
local notation "g!"=> juncture k
local notation "h!"=> juncture k'
-- prove bilinearity.Direct.S.StatePack.Scaling
lemma junctionAdd (k:σ→σ→ℝ)(f g h:P): juncture k (f+g) h= juncture k f h+juncture k g h := by unfold juncture;simp_rw [map_add,add_mul,smul_add,sum_add_distrib]
lemma junta (k:σ→σ→ℝ)(f g h:P): juncture k f (g-h)=juncture k f g-juncture k f h:=by unfold juncture;simp_rw [map_sub,mul_sub,smul_sub,sum_sub_distrib]
lemma jump (k k':σ→σ→ℝ)(f h:P): juncture (k-k') f h=juncture k f h-juncture k' f h:=by unfold juncture;simp_rw [Pi.sub_apply,sub_smul,sum_sub_distrib]
lemma jumping (k k':σ→σ→ℝ)(f h F G:P): juncture k f h-juncture k' F G=juncture (k-k') f h + juncture k' f (h-G)+juncture k' (f-F) G:=by rw [jump,junta]; unfold juncture; simp_rw [_root_.map_sub,sub_mul,smul_sub,Finset.sum_sub_distrib];abel
lemma stove_jump (k k':σ→σ→ℝ)(f h:P): stove k f-stove k' h= stove (k-k') f+ stove k' (f-h):=by
    rw [map_sub]; simp_rw [stokes]; simp only [Pi.sub_apply,sub_div,sub_smul]; simp_rw [sum_sub_distrib]; abel
namespace Paired
lemma widen (h:Paired l x a B p m ξ f g t D E)(H:t≤u)(HX:0≤D)(he:E≤v)(hy:q≤m): Paired l x a B p q ξ f g u D v:=⟨h.input.delta hy H,h.other.delta hy H, h.change.delta hy (mul_le_mul_of_nonneg_right he HX)⟩
lemma addN (h:Paired l x a B p m ξ f g t D E)(s:Paired l x a B p m ξ F H u D v): Paired l x a B p m ξ (f+F) (g+H) (t+u) D (E+v) :=by
   refine ⟨h.input.kit s.input,h.other.kit s.other,?_⟩; rw [show f+F-(g+H)=(f-g)+(F-H) by abel,add_mul]; exact h.change.kit s.change
lemma mulR (h:Paired l x a B p m ξ f g t D E)(s :ℝ): Paired l x a B p m ξ (s • f) (s • g) (|s| *t) D (|s| * E) := by
   refine ⟨h.input.smoky _,h.other.smoky _,?_⟩; rw [← smul_sub,mul_assoc]; exact h.change.smoky _
include H₀
lemma rail (h:Paired l x a B p (m+2) ξ f g t D E): Paired l x a B p m ξ (stove k f) (stove k' g) (b*t) D (t+b*E):=by
   refine ⟨depthUp (add_nonneg H₀.sober H₀.green) H₀.full h.input, depthUp (add_nonneg H₀.sober H₀.green) H₀.group h.other,?_⟩
   rw [stove_jump,show _*D=D*t+b*(E*D) from (by ring)]; exact (bulk_delta H₀.sober H₀.green H₀.step h.input).kit (stab_delta H₀.sober (H₀.group.low (le_add_of_nonneg_right H₀.green)) h.change)
lemma wheel (h:Paired l x a B p (m+1) ξ f g t D E)(s:Paired l x a B p (m+1) ξ F H u D v): Paired l x a B p m ξ (juncture k f F) (juncture k' g H) (2*2^m*(t*(b*u))) D (2*2^m*(t*u + t*b*v+E*b*u)):=by
    refine ⟨union_bulk (add_nonneg H₀.sober H₀.green) H₀.full h.input s.input, union_bulk (add_nonneg H₀.sober H₀.green) H₀.group h.other s.other,?_⟩
    rw [jumping k k' f F g H, reversal k' (f-g) H]; have hx:= (bulk_stem H₀.sober H₀.green H₀.step h.input s.input).kit (mix_f H₀.sober H₀.green H₀.group h.input s.change)|>.kit (mix_f H₀.sober H₀.green H₀.group.loom s.other h.change); exact hx.delta le_rfl (le_of_eq (by ring))
end Paired
namespace Starry
lemma widen (h:Starry l x a B p m ξ f g t D E)(H:t≤u)(HX:0≤D)(he:E≤v)(hy:q≤m): Starry l x a B p q ξ f g u D v:=⟨Quote.widen h.input H hy,Quote.widen h.other H hy,Quote.widen h.change (mul_le_mul_of_nonneg_right he HX) hy⟩
lemma addN (h: Starry l x a B p m ξ f g t D E)(s: Starry l x a B p m ξ F H u D v): Starry l x a B p m ξ (f+F) (g+H) (t+u) D (E+v) :=by
    refine ⟨Quote.addN h.input s.input,Quote.addN h.other s.other,?_⟩; rw [show f+F-(g+H)=(f-g)+(F-H) by abel,add_mul]; exact Quote.addN h.change s.change
lemma mulR (h: Starry l x a B p m ξ f g t D E)(s :ℝ): Starry l x a B p m ξ (s • f) (s • g) (|s| *t) D (|s| * E) := by
   refine ⟨Quote.mulR h.input _,Quote.mulR h.other _,?_⟩; rw [← smul_sub,mul_assoc]; exact Quote.mulR h.change _
include H₀
lemma rail (h:Starry l x a B p (m+2) ξ f g t D E): Starry l x a B p m ξ (stove k f) (stove k' g) (b*t) D (t+b*E):=by
    have ht:= power_delta H₀.sober H₀.green H₀.step h.input (mem_singleton_self x)
    refine ⟨power_hp (add_nonneg H₀.sober H₀.green) H₀.full h.input, power_hp (add_nonneg H₀.sober H₀.green) H₀.group h.other,?_⟩
    rw [stove_jump,show _*D= Eve B x x*(D*t)+b*(E*D) from ?_]; · exact Quote.addN ht (power_hp H₀.sober (H₀.group.low (le_add_of_nonneg_right H₀.green)) h.change)
    simp only [Eve,separation_self, Nat.cast_zero,mul_zero,Real.exp_zero,one_mul]; ring
lemma wheel (h:Starry l x a B p (m+1) ξ f g t D E)(s:Paired l x a B p m ξ F H u D v): Starry l x a B p m ξ (juncture k f F) (juncture k' g H) (2^m*(t*(b*u))) D (2^m*(t*u + t*b*v+E*b*u)):=by
    refine ⟨jumble (add_nonneg H₀.sober H₀.green) H₀.full h.input s.input,jumble (add_nonneg H₀.sober H₀.green) H₀.group h.other s.other,?_⟩
    rw [jumping k k' f F g H]; have hp : a ≤ a+B:= le_add_of_nonneg_right H₀.green
    have he:= Quote.addN (Quote.addN (stem_in H₀.sober H₀.green H₀.step h.input (s.input.soft hp H₀.sober)) (token_turn H₀.sober H₀.green H₀.group h.input s.change)) (jumble H₀.sober (H₀.group.low hp) h.change (s.other.soft hp H₀.sober))
    refine Quote.widen he (le_of_eq ?_) le_rfl; simp only [Eve,separation_self,Nat.cast_zero,mul_zero,Real.exp_zero,one_mul]; ring
end Starry
end YM.MSbar.Whisk
