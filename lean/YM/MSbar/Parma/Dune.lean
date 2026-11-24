import YM.MSbar.Parma.Torch
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Parma
open Function Filter Whisk Lis Measuring Cacao CrossH Push Uniform Lattice RG Pressure Matrix
open Precision Gauge Midpoint Rolling Tramp Exterior Tree Wilson Laurent Bloch Wave UVNext.PricedKernels
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge} {c n:Side}{S:StepData c n}(F: Forest S.ratio)
local notation "X"=>Primary n G
local notation "Y"=>Primary c G
local notation "Φ"=> Key F G
local notation "K"=>Joint F G
local notation "T"=> S.ratio
local notation "Ψ"=>address F G
local notation "θ"=>Measuring.chart n G
local notation "⌂"=>Positions (Joint F G)
local notation "O"=> Tramp.path S.ratio G
variable {μ C Λ :ℝ}{j s p N:ℕ}{V: KernelChoices}
variable (Z:Uniform.Before G μ C j V N)(J:ChartRatio G)
variable (τ:S.Choices)(hj:S.patch.J=j)(hv:S.kernel=V)(h:Bid.Larger (G:=G) S) (hJ:LocalRatio J)
variable (l:Clip)(R:PathData G)(hR:R.Bounds l μ C Λ)
noncomputable def swatch (F:Forest S.ratio)(τ:S.Choices)(l:Clip)(R:PathData G) : Matrix (Joint F G) (Joint F G) ℝ := (Rolling.straight F G)*(Uniform.block (priced F τ l R) 0)⁻¹*(Rolling.straight F G).transpose
local notation "L"=>swatch F τ l R
local notation "B"=> Z.tables l S.patch -- macro fields notation
include Z h hv hj hR
set_option quotPrecheck false
local notation "t'"=> (Z.tables l S.patch).rate
local notation "ν"=> (Z.tables l S.patch).gap
lemma peacock (i j:Joint F G): gained (Z.tables l S.patch).rate (address F G i) (address F G j)*|swatch F τ l R i j| ≤ (ν/2/2)⁻¹:=by
    obtain ⟨hZ, -⟩:= Z.receipt F τ hR h hj hv -- specs health
    let C':=Uniform.block (priced F τ l R) 0; let v:= B; have hp:=hZ.reserveH_pos; obtain ⟨hv,hl,H⟩:= hZ.priced_inverse 0 (Metric.mem_closedBall_self hp.le)
    rw [swatch,sail_cov]; cases i <;> cases j
    all_goals first| (dsimp only; rw [abs_zero,mul_zero]; exact inv_nonneg.mpr (half_pos (half_pos hZ.pos_m)|>.le))| skip
    next i j=>
        let k:= ν/2/2; let g(y: Key F G):= Ψ (.inr y); have he:|C'⁻¹ i j| ≤ k⁻¹*Decay t' (g i) (g j):= hl i j
        let u:=gained t' (g i) (g j); refine (mul_le_mul_of_nonneg_left he (gained_pos ..|>.le)).trans_eq ?_; unfold gained Decay; rw [mul_left_comm, ← Real.exp_add]; rw [neg_mul,add_neg_cancel,Real.exp_zero,mul_one]
omit Z h hv hj hR
-- taps.Syrup with matching anchor exactly.No finite volume loss
lemma essay (j: X)(v:Joint F G): taps F G j v=(stamp F G (pushG F (bolt v))) j:=by
    let p:Positions (Joint F G):= Pi.single v 1; have hp:p=bolt v:=by ext i; by_cases he:i=v<;> simp [p,bolt,he]
    rw [←hp]
    have ht: stamp F G (pushG F p)= taps F G*ᵥ p :=by unfold taps; rw [LinearMap.toMatrix'_mulVec];rfl
    rw [ht]; unfold p; simp [Matrix.mulVec_single]
lemma clap (r:ℝ)(j:X)(i:K): gained r (θ j) (Ψ i)* |taps F G j i| ≤ 1:=by
    rw [essay]
    obtain ⟨⟨j,t⟩,s⟩:=j; obtain ⟨t,rfl⟩:= axisEquiv.surjective t; change gained r j (Ψ i)* |stamp F G _ ((j,Exterior.coord t),s)| ≤ _; rw [ruler]; split; next _=>simp
    next hh=>
        change _*|bolt i (Sum.inr (⟨(j,t),hh⟩,s))|≤ _; by_cases he:i= .inr (⟨(j,t),hh⟩,s)
        · rw [he]; simp [gained, address,bolt] -- fix
        simp [bolt,Ne.symm he]
lemma syrupLoop {ι: Type} [Fintype ι] {a b:ℝ}{s:ℕ}(p:ι→ Site n)(f: Matrix ι ι ℝ)(ha:0 ≤ a)(h:Syrup p p a s f b) : LoopNet p a s f b:=by
     let KS(i j:ι):= skim p p a s i j; have ht(i j): liftW a s (separation (p i) (p j)) ≤ KS i j:=by
           let d:ℝ:= separation (p i) (p j); apply inc s ha (by positivity); change d ≤ 2*d; linarith only [Nat.cast_nonneg (α:=ℝ) (separation (p i) (p j))] -- unfold
     refine ⟨zero_le_one.trans h.cash,fun i=>?_ ,fun j=>?_ ⟩
     · refine le_trans (Finset.sum_le_sum fun j _=>?_) (h.leftP i); rw [mul_comm]; exact mul_le_mul_of_nonneg_right (ht i j) (abs_nonneg _)
     refine le_trans (Finset.sum_le_sum fun i _=>?_) (h.rightP j); rw [mul_comm]; exact mul_le_mul_of_nonneg_right (ht i j) (abs_nonneg _)
end YM.MSbar.Parma
