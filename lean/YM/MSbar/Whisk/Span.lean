import YM.MSbar.Whisk.Plait
import YM.Corona.Fit
/-! One norm through all boundary clips and orientation operations. Use *diameter*, unions can concatenate exactly. Later suppress exponential when projecting low. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Whisk
open Function Filter Finset
open scoped BigOperators Classical
variable {σ ι A:Type} [Fintype σ]
open Lattice
variable {n:Side} (l : σ→Site n) {W Y Z:Finset (Site n)} {x y z:Site n} {m p q :ℕ} {r a b t:ℝ}

def extent (W:Finset (Site n)) := Finset.sup W (fun i=> Finset.sup W fun j=> separation i j)
lemma curve (he:x∈W)(hf:y∈W): separation x y ≤ extent W:= le_trans (Finset.le_sup (f:=fun j=> separation x j) hf) (Finset.le_sup (f:=fun i=> Finset.sup W (fun j=>separation i j)) he)
lemma yard (h:∀ i∈W,∀ j∈W,separation i j ≤p): extent W≤p:= Finset.sup_le (fun i hi=> Finset.sup_le (fun j hj=> h i hi j hj))
lemma intr (h:W ⊆ Y): extent W≤ extent Y:= yard fun _ ha _ hb=> curve (h ha) (h hb)
lemma embrace (h : W⊆Y∪Z)(he:x∈Y)(hf:y∈Z) : extent W ≤extent Y+separation x y+extent Z := by
   apply yard; intro i hi j hj
   have hp(i j : Site n)(hx:i∈Y)(hy:j∈Z) : separation i j ≤ _ := le_trans (separation_triangle i x j) (Nat.add_le_add (curve hx he) ((separation_triangle x y j).trans (Nat.add_le_add_left (curve hf hy) (separation x y))))
   rcases Finset.mem_union.mp (h hi) with ha|ha<;> rcases Finset.mem_union.mp (h hj) with hb|hb
   · have he:= curve ha hb; omega
   · exact (hp i j ha hb).trans_eq (by omega)
   · rw [separation_comm]; exact (hp j i hb ha).trans_eq (by omega)
   have he:=curve ha hb;omega
-- multiplicative currency ν torsion.W also polynomial.
def liftW (a:ℝ)(p:ℕ)(d:ℕ) := (1+(d:ℝ))^p* Real.exp (a*d)
lemma wpos (a:ℝ)(p d:ℕ):0 < liftW a p d:=by unfold liftW; positivity
lemma w_start (h:0≤a)(p d:ℕ):1≤liftW a p d:=one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by simp : 1≤1+(d:ℝ))) (Real.one_le_exp (mul_nonneg h (by positivity)))
lemma w_triangle (a : ℝ)(p x y:ℕ) : liftW a p (x+y) ≤ liftW a p x*liftW a p y:=by
   have hp:1+(x:ℝ)+y≤(1+x)*(1+y):=by push_cast; nlinarith [Nat.cast_nonneg (α:=ℝ) x,Nat.cast_nonneg (α:=ℝ) y]
   unfold liftW; push_cast; rw [mul_add,Real.exp_add,← add_assoc (1:ℝ)]; exact le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hp _) (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)) (le_of_eq (by rw [mul_pow]; ring))
lemma w_more (h:m≤p)(hc:0≤a)(n:ℕ) :liftW a n m ≤ liftW a n p:=by unfold liftW;gcongr
lemma w_cast (h : W⊆Y∪Z)(he:x∈Y)(hf:y∈Z)(ha:0≤a)(p:ℕ): liftW a p (extent W) ≤ liftW a p (extent Y)*liftW a p (separation x y)*liftW a p (extent Z):=by refine (w_more (embrace h he hf) ha p).trans ((w_triangle a p _ _).trans (mul_le_mul_of_nonneg_right (w_triangle a p _ _) (wpos ..|>.le)))
-- socket l list. major books with anchors batch

def zone (W:Finset (Site n)) (T : List σ) : Finset (Site n) := W∪(List.map l T).toFinset
def spread (l:σ→Site n)(W:Finset (Site n)) (a:ℝ)(p:ℕ)(T : List σ) := liftW a p (extent (zone l W T))
lemma effect (a:ℝ)(p) (W:Finset (Site n))(T:List σ):0< spread l W a p T:=wpos ..
lemma radius_go {i:σ}{T :List σ}(h:i∈T)(hf:y∈W)(ha:0≤a)(p:ℕ): liftW a p (separation y (l i)) ≤ spread l W a p T:=w_more (curve (y:=l i) (Finset.mem_union_left _ hf) (Finset.mem_union_right W (List.mem_toFinset.mpr (List.mem_map.mpr ⟨i,h,rfl⟩)))) ha p
lemma added (T:List σ)(v : σ): zone l W (v::T) = insert (l v) (zone l W T):=by ext x; simp [zone]
end YM.MSbar.Whisk
