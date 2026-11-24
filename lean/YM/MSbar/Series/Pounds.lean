import YM.MSbar.Series.Prim
import Mathlib.Data.Nat.Choose.Sum
/-! Power sums for the loop weights. Multiplicative identity after a complete lattice read
(no multiplication of distributions on coincident points). -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Category
open Function Finset Filter
open scoped BigOperators Classical
variable {X Y Z : Type*} [AddCommGroup X][Module ℂ X][AddCommGroup Y][Module ℂ Y][AddCommGroup Z][Module ℂ Z] {f g: Form X} {u:Form Y} {c:ℂ} {k m j:ℕ}

-- use `b : ℕ→ℂ` satisfying add_add via ext; actual slope
variable (b:ℕ→ℂ)
def read (i m:ℕ): Form X→ₗ[ℂ] X:={toFun:= fun x=>∑ v∈range (m+1),(b v)^i • x v,map_add':=fun x y=> by simp [sum_add_distrib],map_smul':=fun u x=> by simp only [smul_sum, RingHom.id_apply,Pi.smul_apply]; apply sum_congr rfl; intro i _; apply smul_comm}
lemma novel {f:Form X}: read b k m f= ∑ v∈range (m+1),(b v)^k • f v:= rfl
lemma single (x:X)(k:ℕ)(hu:j≤m): read b k m (Pi.single j x)=(b j)^k • x:=by rw [novel,sum_eq_single j]; simp; intro i _ H; simp [H]; intro h; simp at h; omega
variable (hb:∀ x y,b (x+y)=b x+b y)
include hb
-- need ∑ range; add_pow convention check
lemma extends_cover (hf:Cap m f)(hu:Cap j u)(d:ℕ)(P:X→ₗ[ℂ] Y→ₗ[ℂ] Z):
    read b d (m+j) (knot P f u)= ∑ i∈ range (d+1), (d.choose i:ℂ) • P (read b i m f) (read b (d-i) j u) := by
    rw [axes hf,axes hu]; simp_rw [map_sum, LinearMap.sum_apply,map_sum,Finset.smul_sum]; nth_rw 2 [sum_comm] -- f outer? inspect
    refine sum_congr rfl fun k hk=>?_ ; -- inner
    rw [sum_comm]; apply sum_congr rfl; intro x hx; rw [knot_single,single _ _ _ (by simp at hk hx; omega),hb,add_pow,sum_smul]; apply sum_congr rfl; intro i hi; rw [single _ _ _ (by simp at hx; omega),single _ _ _ (by simp at hk; omega),map_smul P, LinearMap.smul_apply,map_smul]; module
lemma backwards (A:X→ₗ[ℂ]Y)(d:ℕ) : read b d (m+1) (sea A f)=∑ i∈ range (d+1), ((d.choose i:ℂ)*(b 1)^(d-i)) • A (read b i m f):=by
    simp_rw [novel,sum_range_succ' (f:=fun i=>b i ^d • sea A f i),sea_zero,sea_pos,smul_zero,add_zero,map_sum,map_smul,smul_sum,smul_smul]; rw [sum_comm]; refine sum_congr rfl fun k hk=> ?_; rw [hb,add_pow,sum_smul]; apply sum_congr rfl; intro i hi; congr! 1; ring
omit hb in
lemma read_lm (A:X→ₗ[ℂ]Y)(m:ℕ): read b j m (act A f)= A (read b j m f):=by simp [novel]
end YM.MSbar.Category
