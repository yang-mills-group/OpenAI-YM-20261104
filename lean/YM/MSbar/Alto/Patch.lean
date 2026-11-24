import YM.MSbar.Alto.Leagues
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Alto
open Function Filter Whisk Lis Measuring Cacao CrossH Push Uniform Lattice RG Pressure Matrix
open Precision Gauge Midpoint Rolling Tramp Exterior Tree Wilson Laurent Bloch Wave Parma Tin Bronze Asymptotics Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge}
section
variable (G:Gauge)(V:Fees) (p s n:ℕ)(a:ℝ)(g:Side)
local notation "Π!"=>spat G V g s n
local notation "μ!"=>Dean n
local notation "χ"=>Dean (n-1)
noncomputable def prerequisites (G:Gauge)(V:Fees)(g:Side)(r s:ℕ)(a:ℝ): Prop:= shares G V g r s a <2⁻¹ ^ Dean r∧ shares G V g r s a*(1+V.bc)< 2⁻¹^ Dean r -- notation inverse default
structure Host (G:Gauge)(V:Fees)(g:Side)(p s:ℕ)(a:ℝ): Prop where
   expedient : ∀ i∈Finset.Icc 1 p, prerequisites G V g i s a
   spark: 3 ≤ V.axis
   arity:6 ≤ s
   orbit : 0≤a
   ok : 0 ≤ V.pre ∧ 0≤ V.tilt∧0≤ V.shape
   fine : 0 ≤ V.bf∧0≤ V.bc
   stars: ∀ i∈ Finset.Icc 1 p, 0 ≤ shares G V g i s a
   path: 0≤ V.farms ∧ 0≤ V.c1∧0≤V.c2∧ 0≤V.c3 ∧0≤V.c4
-- stars follow
lemma steady (he:0 < n)(hp:prerequisites G V g n s a) : ∀ᶠ t:ℝ in atTop,∀ v:ℝ, t/2≤v → let X:=t ^ μ!; let q:=v^μ!; let D:= Π! a t; let T:= D+Bronze.salary n (t^χ) (t^χ); D ≤ q ∧ T*(1+V.bc) ≤ q ∧ T/t^2 +Bronze.straw (t^χ) n ≤ q:=by
    let h:= shares G V g n s a; let C:ℝ:=2⁻¹ ^μ!
    have hc:0<C:=pow_pos (by norm_num) _; filter_upwards [eventually_gt_atTop (0:ℝ), (Alto.brush G V s n a g he).eventually (ge_mem_nhds hp.1), ((risePost G V s n a g he).mul_const (1+V.bc)).eventually (ge_mem_nhds hp.2), (clears G V s n a g he).eventually (ge_mem_nhds hc)] with t ht ht₀ ht₁ ht₂ w hw q D TS
    let X:= t^μ!
    have hv(t':ℝ)(hh:t'/X≤ C):t'≤ q:=by
       have hp:= (div_le_iff₀ (pow_pos ht μ!)).mp hh; exact hp.trans (le_trans (le_of_eq (show C*X=(t/2)^μ! from (by unfold C X; rw [div_pow, div_eq_mul_inv, inv_pow,mul_comm]))) (pow_le_pow_left₀ (by positivity) hw _))
    refine ⟨hv _ ht₀,hv _ ?_,hv _ ht₂⟩; rw [mul_comm TS, mul_div_assoc,mul_comm]; exact ht₁
-- a-monΦ limited shape. prove
open Cane
lemma favMon {x d A b:ℝ}(p:ℕ)(h:a ≤ x)(hm:0≤d)(ht:0≤b):value a d A b s p ≤ value x d A b s p:=by
   unfold value candle; have he:(0:ℝ) ≤ teeth p:=zero_le_one.trans (jaws p); -- A d binder orientation call `value a D η E`; A =η; D requires 0
   unfold Measuring.factor; gcongr <;> simp
end
end YM.MSbar.Alto
