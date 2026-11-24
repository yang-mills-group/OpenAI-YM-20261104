import YM.MSbar.Parma.Curry
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Parma
open Function Filter Whisk Lis Measuring Cacao CrossH Push Uniform Lattice RG Pressure Matrix
open Precision Gauge Midpoint Rolling Tramp Exterior Tree Wilson Laurent Bloch Wave UVNext.PricedKernels
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge} {c n:Side}{S:StepData c n}(F: Forest S.ratio)
local notation "X"=>Primary n G
local notation "Y"=>Primary c G
local notation "K"=>Joint F G
local notation "T"=> S.ratio
local notation "Ψ"=>address F G
local notation "θ"=>Measuring.chart n G
local notation "⌂"=>Positions (Joint F G)
local notation "O"=> routeN S.ratio
variable {μ C Λ :ℝ}{j s p N:ℕ}{V: KernelChoices}
variable (Z:Uniform.Before G μ C j V N)(J:ChartRatio G)
variable (τ:S.Choices)(hj:S.patch.J=j)(hv:S.kernel=V)(h:Bid.Larger (G:=G) S) (hJ:LocalRatio J)
noncomputable def steamB (α:ℝ)(s p:ℕ)(A:Patch) (Z:Uniform.Before G μ C j V N) := cities 4 (noiseCost A) * rugL α (priceArc A G V N Z.Z Z.lc Z.W) s (noiseCost A) p (cities (townCost G) (noiseCost A))
noncomputable def coreK (α:ℝ)(s p:ℕ)(J:ChartRatio G):= (cities 4 0:ℕ)* rugL α (feeJ (p+1) J) s 0 p (cities (townCost G) 0)
noncomputable def cream (α:ℝ)(s p:ℕ)(S:Patch)(Z:Uniform.Before G μ C j V N)(J:ChartRatio G):ℝ:= steamB α s (p+2) S Z + coreK α s p J -- adjust
include h Z hv -- kernel equality convert
lemma tau (p:ℕ) (i: Bond c)(hp:p+1≤N): Lumber (address F G) (routeN T i) (noiseCost S.patch) (arch F τ i) p (priceArc S.patch G V N Z.Z Z.lc Z.W):=by
    have he:= august F τ i (le_trans (by decide) Z.n_ok) Z.labels Z.focus Z.exp Z.log
    rw [hv] at he
    exact native (arch (G:=G) F τ) i p _ _ _ _ (he.1.of_le le_top) (he.2 _ hp) (Eventually.of_forall fun x=> behove F τ i x h.1)
lemma scorched (p m:ℕ)(a:ℝ)(hp:p+1 ≤ N)(ha:0≤a):Tokew (address F G) a s m 0 (potter (pushChart F G τ) (p+1)) (steamB a s p S.patch Z) :=by -- j reused; fix arbitrary
   let C:=priceArc S.patch G V N Z.Z Z.lc Z.W; let i:Bond c:= Classical.arbitrary _; have hp(i): Lumber Ψ (O i) (noiseCost S.patch) (arch F τ i) p C:= tau F Z τ hv h _ i hp
   exact scaleBook (arch F τ) hp (hp i).zero ha _ (Eventually.of_forall fun x=>robe F τ x) _ _ (town F) (flagC T Prod.fst (powerP c Axis)) _
variable (a:ℝ)(f:Nesting G n)
local notation "I"=> splitV (singularity (swung F J) 0) -splitV (singularity (pushChart F G τ) 2)
local notation "Δ"=>PowerSeries.coeff
include hJ
lemma billing (m q:ℕ)(hp:q+1+2≤N)(ha:0≤a):Tokew Ψ a s m 0 (PowerSeries.coeff (q+1) (splitV (singularity (swung F J) 0)-splitV (singularity (pushChart F G τ) 2))) (cream a s q S.patch Z J):=by
    rw [map_sub]; simp only [splitV,map_sub,PowerSeries.coeff_C_of_ne_zero (show q+1≠0 by omega),sub_zero]; unfold singularity; simp only [PowerSeries.coeff_mk,add_zero]; let g:=potter (pushChart F G τ) (q+2+1)
    have hf:= cast F J hJ a s q m ha; have hp := scorched (s:=s) F Z τ hv h (q+2) m a (by omega) ha; -- m
    rw [sub_eq_add_neg,show q+1+2=q+2+1 from (by omega),← neg_one_smul ℝ g]; refine Tokew.delta (hf.kit (hp.smoky (-1))) le_rfl ?_; unfold cream coreK;simp; linarith
end YM.MSbar.Parma
