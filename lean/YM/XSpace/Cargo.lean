import YM.XSpace.Crisps
/-! # Rewrite contributions where a U is replaced. Shifted/direct order-one mark formulas -/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Graph3
open Function Set Filter Lattice Trace Chart2 Maxwell Maxwell.Free Foundation MvPolynomial Structure1 Chiral Finsupp Mu Next.Rank.Normal Stall Pages Contraction
open scoped Topology BigOperators InnerProductSpace Classical
variable {G:Gauge} (W:Initialize G)(g:G.Simple)(z x y:Cover){d:ℕ}
local notation "A" => b_w W z
local notation "X" => u_line g W x
local notation "Y" => u_line g W y
local notation "J" => Name G
lemma γ_capped {P Q:Stamp G} (e:ℕ)(h: Hom P d)(hp: Q∈ DegZ (UnitIndex G) e)(H:e<d): F2 G P Q=0:=by
  rw [← clasp, known hp,map_sum]; apply Finset.sum_eq_zero; intro i hi; rw [clasp]; exact γ_between P _ h (show Hom _ i from weightedHomogeneousComponent_mem ..) (ne_of_gt (lt_of_le_of_lt (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) H)) -- .. notation fix
include g in
lemma lower2 (p:Stamp G)(h: p∈DegZ (UnitIndex G) 2): F3 A p (u_w W y)=0:=by
  have ht(j:J): F3 A p (harp (Y j)*harp (Y j))=0:=by
    rw [pp,γ_capped 0 (b_power W g z) (ξ_low _ (ξ_low (n:=1) _ h)) (by decide),γ_capped 1 (ξ_rule _ (b_power W g z)) (ξ_low _ h) (by decide),double_off W g _ (fares_on g (W.surveys _) false j y),F2,map_zero];simp
  rw [u_w,under g]; unfold F3 u_r; rw [← clasp,map_smul,map_smul,map_sum,map_sum]; change (2:ℂ)⁻¹ • (∑ j:J,F3 A p (harp (Y j)*harp (Y j)))=0; rw [Finset.sum_eq_zero (s:=Finset.univ) (fun i _=> ht i),smul_zero]

abbrev station (i j k:J):=peek G (Ξ (b_line g W z i) (Ξ (Y k) (u_s W x j)))
def anomaly (i j:J):ℂ := col (X i) (Y j)*F2 G (Ξ (Y j) A) (u_s W x i)
lemma carry (i j:J) : F2 G (Ξ (Y j) A) (Ξ (Y j) (u_s W x i*u_r g W x i))= anomaly W g z x y i j+scoreX W g z x y (station W g z x y) i j:=by
  let a:=u_s W x i; let b:= u_r g W x i; let T:= Y j; let u:= X i; let P:= Ξ T A
  rw [ξ_mul, show Ξ (Y j) (u_r g W x i)=_ from (ξ_harp (Y j) (X i)), mul_comm (u_s W x i),C_mul', mul_comm _ (u_r g W x i),← clasp,map_add,map_smul,clasp,clasp] -- rewrites all
  congr 1
  change F2 G P (harp u * Ξ T a)=_
  rw [bound_up P, ζ_hop, ← clasp (Ξ T a) (Ξ u _)] -- need order
  unfold P; rw [double_strike W g]; simp_rw [map_sum, map_smul]; unfold scoreX; refine Finset.sum_congr rfl fun k _=> Finset.sum_congr rfl fun m _=> Finset.sum_congr rfl fun n _=>?_ ; rw [clasp,bound_up (Ξ T a),ζ_line];rfl

def ups := ∑ i:J,∑ j:J,anomaly W g z x y i j
lemma completionU : F3 A (u_1 W x) (u_w W y)= ups W g z x y+playAll W g z x y (station W g z x y):=by
  rw [underneath g W x, u_w, under g W y]; -- order?
  let Q(i:J):= u_s W x i*u_r g W x i; let K(i:J):= u_r g W y i* u_r g W y i
  have he(i j:J):F3 A (Q i) (K j) = 2*(anomaly W g z x y i j+ scoreX W g z x y (station W g z x y) i j):=(p22 _ _ _ (b_power W g z) ((brace_degree ..).mul (strongs ..))).trans (congr_arg (2*·) (carry W g z x y i j))
  unfold F3; change F2 G A (tie G (∑ i,Q i) ((2:ℂ)⁻¹ • ∑ i,K i))=_; rw [← clasp]; simp_rw [map_sum,LinearMap.sum_apply,map_sum,map_smul]; -- rearrange
  simp_rw [map_sum,Finset.smul_sum]; change (∑ i:J,∑ j:J,(2:ℂ)⁻¹ • F3 A (Q i) (K j))=_; simp_rw [he,smul_eq_mul,inv_mul_cancel_left₀ (by norm_num : (2:ℂ)≠ 0),Finset.sum_add_distrib]; rfl
end YM.XSpace.Graph3
