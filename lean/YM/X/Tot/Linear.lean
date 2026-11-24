import YM.X.Tot.Mesa
/-!
# Integrals, mantle & elected(outflow distinct vertices); all linearity exact. Keep CurtWords independent of vertex. -/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Tot
open Lattice Wilson Next.Rank Normal MvPolynomial Function Filter Set MeasureTheory Asymptotics
open PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Reed Shelf
open Stems hiding X
open Ocean Haze Fielding Print Fund Tri
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{d k m l:ℕ} {V W I:Type*} {r R:ℝ}
local notation "fℕ"=>(atTop:Filter ℕ)
variable (q:ℕ+)
local notation "Ψ"=> Billboard G q
local notation "Λ"=> Weave q
local notation "𝓟"=> Foam G
local notation "Q"=> (qu q G)
variable (c:ℂ) (L: Weave q) (A B C' V Z: Billboard G q)
def mantle : ℕ→ℂ:= crow q (L * fun i z=> majority (Q i) (V i z) (A i z) (B i z) (C' i z))
def relevant : ℕ→ℂ:= crow q (fun i z=> school (Q i) (A i z) (B i z) (C' i z) (V i z))
local notation "M"=> mantle q L
local notation "R"=> relevant q
lemma maj_swap : M A B C' V=M A C' B V:= by ext1 i; unfold mantle crow; apply congr_arg; apply Finset.sum_congr rfl; intro z _; dsimp only [Pi.mul_apply]; rw [majority_sym]
lemma relev : relevant q A B C' V = crow q (fun i z=> space (Q i) (A i z) (B i z) (C' i z) (V i z))- mantle q 1 A B C' V-mantle q 1 B A C' V-mantle q 1 C' A B V:= by
   unfold relevant mantle; simp only [one_mul, school]; rw [← crowd_sub,← crowd_sub,← crowd_sub]; rfl
-- simplify ≠ use local simp attributes at proof invocation; small code
lemma mantle_zero : M A B C' 0=0:= by unfold mantle; ext1; simp [crow, majority, mzero]
lemma mantle_vert_up : M A B C' (V+Z) = M A B C' V + M A B C' Z:= by ext1 k; simp [mantle, crow, majority, madd₀,tri_plus, Pi.mul_apply,mul_add,Finset.sum_add_distrib]
lemma mantle_vert_scale (c:ℕ→ℂ) : M A B C' (ensign q c • V)= c * M A B C' V:= by
   unfold mantle; let f:= fun (i:ℕ)(z:Site (side q i))=> majority (Q i) (V i z) (A i z) (B i z) (C' i z); rw [show L*_= (L*f)*ensign q c from ?_, crowd_time,mul_comm]; ext1 i; ext1 z; change L i z*tri _ (multi _ (A i z) (c i • _)) _ _=(L i z*f i z)*c i; rw [mscale,tri_scale]; unfold f majority; simp [mul_right_comm,mul_assoc,mul_comm (c i) _]
lemma mantle_scale_v : M A B C' (c • V)= c • M A B C' V:= mantle_vert_scale q L A B C' V (fun _=>c) -- defeq?
lemma mantle_add : M (A+Z) B C' V=M A B C' V+M Z B C' V:= by ext1 k; simp [mantle,crow, majority,madd,tri_plus, Finset.sum_add_distrib, mul_add]
lemma mantle_add' : M A (B+Z) C' V=M A B C' V+M A Z C' V:= by ext1 k; simp [mantle,crow, majority,tri_plus₁, Finset.sum_add_distrib, mul_add]
lemma mantle_scale (c:ℕ→ℂ) : M (ensign q c • A) B C' V=c*M A B C' V:= by ext1 k; change volS q k*(∑ z:Site (side q k), L k z* majority (Q k) (V k z) (c k • A k z) (B k z) (C' k z))= c k * M A B C' V k; simp_rw [mantle,crow,majority,mscale',tri_scale,Pi.mul_apply,Finset.mul_sum];apply Finset.sum_congr rfl; intro i _; simp_rw [smul_eq_mul];ring
lemma mantle_scale' (c:ℕ→ℂ) : M A (ensign q c • B) C' V=c*M A B C' V:= by ext1 k; change volS q k*(∑ z:Site (side q k), L k z* majority (Q k) (V k z) (A k z) (c k • B k z) (C' k z))= c k * M A B C' V k; simp_rw [mantle,crow,majority,tri_scale₁,Pi.mul_apply,Finset.mul_sum];apply Finset.sum_congr rfl; intro i _; simp_rw [smul_eq_mul];ring
lemma mantle_const (D:Billboard G q)(a:ℂ) : M (a • D) B C' V=a • M D B C' V:= mantle_scale _ _ _ _ _ _ (fun _=>a) -- parameters
lemma elected : R A B C' V= R B C' A V := by ext1 i; unfold relevant crow; apply congr_arg; apply Finset.sum_congr rfl; intro z _; dsimp only; rw [school_sym (A:=A i z), school₁ (A:=(B i z))]
lemma elect₁ : R A B C' V= R A C' B V:= by ext1 i; unfold relevant crow; apply congr_arg; apply Finset.sum_congr rfl; intro z _; dsimp only; rw [school₁]
lemma relevant_v : R A B C' (V+Z)= R A B C' V+R A B C' Z:= by
    ext1 i; rw [relev,relev,relev,mantle_vert_up,mantle_vert_up,mantle_vert_up]; unfold crow; simp only [Pi.add_apply,Pi.sub_apply, space_add, Finset.sum_add_distrib,mul_add]; ring
lemma relevant_zero : relevant q A B C' 0=0:= by rw [relev,mantle_zero,mantle_zero,mantle_zero]; simp_rw [Pi.zero_apply,qu_zero]; ext1; simp [crow]
lemma rv_scale (c:ℕ→ℂ): R A B C' (ensign q c • V)= c * R A B C' V:= by
   rw [relev,relev,mantle_vert_scale,mantle_vert_scale,mantle_vert_scale]; simp only [mul_sub]; let f:= fun (i:ℕ)(z:Site (side q i))=> space (Q i) (A i z) (B i z) (C' i z) (V i z); rw [show c*crow q f=crow q (f*ensign q c) from Eq.trans (mul_comm ..) (crowd_time ..).symm]; congr 4; ext1 i; ext1 z; exact Eq.trans (space_scale ..) (mul_comm ..)
lemma rv_const : relevant q A B C' (c • V)= c • relevant q A B C' V:= rv_scale q A B C' V (fun _=>c)
end YM.PositionX.Tot
