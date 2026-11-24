import YM.FormalBulk08.Lava.Ignis

/-! Tracing and linking formulas written as local tsums (tests for
infinite cover below). `r=0` not used in those estimates. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Lava
open Series Wick Orb MvPolynomial
open scoped BigOperators Classical
variable {V : Type*} (q : V→V→ℝ)
def stare {r : ℕ} (T : Tile V (r+1+1)) : Tile V r := fun v=> ∑' a: V × V, halve (q a.1 a.2)*((r+2:ℕ):ℝ)* ((r+1:ℕ):ℝ)*shed (shed T a.2) a.1 v
def bond {m n : ℕ} (T : Tile V (m+1)) (S : Tile V (n+1)) : Tile V (m+n) := fun v => ∑' a: V × V, halve (q a.1 a.2)* ((m+1:ℕ):ℝ) * ((n+1:ℕ):ℝ) * clutch (shed T a.1) (shed S a.2) v
lemma Agate.staring {r : ℕ} {T : Tile V (r+1+1)} (h : Agate T) : Agate (stare q T) := by
   intro v s; change (∑' a: V × V, _) = ∑' a: V×V, _
   exact tsum_congr fun a=> by rw [(h.shed a.2).shed a.1 v s]
lemma stare_nil (r : ℕ) : stare q (0 : Tile V (r+1+1))=0 := by funext v; simp [stare,shed]
lemma bond_void {m n : ℕ} (S : Tile V (n+1)) : bond q (0 : Tile V (m+1)) S=0 := by funext v; simp [bond,clutch,shed]
lemma bond_wane {m n : ℕ} (T : Tile V (m+1)) : bond q T (0 : Tile V (n+1))=0 := by funext v; simp [bond,clutch,shed]
lemma sand_nil (r : ℕ) : sand (0 : Tile V r)=0:=sand_fixed (agate_zero _)

variable [Fintype V]
lemma facade_stare {r : ℕ} {T : Tile V (r+1+1)} (h : Agate T) : facade _ (stare q T)= press q (facade _ T) := by
   have hv : stare q T=∑ a,∑ b,(halve (q a b)* ((r+1+1:ℕ):ℝ) * ((r+1:ℕ):ℝ)) • shed (shed T b) a := by funext v; rw [stare,tsum_fintype];simp [Finset.sum_apply, Fintype.sum_prod_type,add_assoc]
   simp_rw [hv,map_sum, map_smul,press_eq,facade_slope _ h,pderiv_C_mul];simp_rw [smul_eq_C_mul,map_mul]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; rw [facade_slope _ (h.shed j)]; ring
lemma facade_bond {m n : ℕ} {T : Tile V (m+1)} {S : Tile V (n+1)} (h : Agate T) (k : Agate S) : facade _ (sand (bond q T S)) = atomProduct q (facade _ T) (facade _ S) := by
   have hv : bond q T S=∑ a,∑ b,(halve (q a b)* ((m+1:ℕ):ℝ) * ((n+1:ℕ):ℝ)) • clutch (shed T a) (shed S b) := by funext v; rw [bond,tsum_fintype]; simp [Finset.sum_apply,Fintype.sum_prod_type]
   simp_rw [sand_facade,hv,map_sum,map_smul,atomProduct,facade_slope _ h,facade_slope _ k, facade_clutch, smul_eq_C_mul,map_mul]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring
lemma marble_stare (p : TypeR V) (r : ℕ) : marble r (press q p)=stare q (marble (r+1+1) p) := by
   apply facade_unique (marble_agate _ _) ((marble_agate _ _).staring q)
   rw [marble_grade,facade_stare q (marble_agate _ _),marble_grade]; simp only [press_eq,map_sum, homogeneousComponent_C_mul,comp_fuses]
end YM.FormalBulk08.Lava
