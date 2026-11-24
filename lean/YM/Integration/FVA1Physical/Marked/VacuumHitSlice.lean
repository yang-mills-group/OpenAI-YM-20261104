import YM.Extra.MULTISOURCE_BOUNDS.Root
import YM.RG.ActivityBounds
import YM.Push.ABSOLUTE_SUMS.Basic

/-! Full countable array of native masked vacuum rows meeting any one of a
finite, possibly widely separated family of physical source locations.
Retaining an excess cover diameter gives a further exponential gain.
Each row is tested at its own independently selected full group input. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace YM.Integration.FVA1Physical.Marked.Inherited
open Finset MeasureTheory Lattice RG YM.Wilson Push.AbsoluteSums
open Extra.Multi
open scoped BigOperators Classical
variable {G:Gauge}{n:Side}(Q:Activities G n)(p:BudgetPoint)

def incident (X:Support n)(cut:ℕ)(i:ℕ):Prop:=
    (∃ x∈X,x∈(Q.reg i).support) ∧ cut≤coverNumber p.B (Q.reg i).support

def sliceRow (X:Support n)(cut i:ℕ)(U:Config G n):ℝ:=by
  classical
  exact if incident Q p X cut i then Q.regularOccurrence p i U else 0

def sliceLog (X:Support n)(cut:ℕ)(U:Config G n):ℝ:=∑' i,sliceRow Q p X cut i U

def sliceFare (p:BudgetPoint)(X:Support n)(cut:ℕ)(δ:ℝ):ℝ:=
    Real.exp (-(p.supportExponent-1)*cut)*(X.card*(siteFactor p.B*δ))

/-- The witnesses are the original center-based physical regular charges
and the full support/hit tariff retains the entire exponent minus one. -/
theorem vacuum_hit_credit {δ:ℝ}(paid:Q.EBound p δ):
    ∃b:ℕ→ℝ,(∀i,p.supBounds (Q.reg i).site (Q.reg i).support (Q.E i) (b i)) ∧
      (∀x:Site n,SumBudget (fun i=>if (Q.reg i).site=x then p.mass (Q.reg i).support (b i) else 0) δ) ∧
      Ac.Hit (fun i=>(Q.reg i).support) p.B b (p.supportExponent-1) (siteFactor p.B*δ):=by
  obtain ⟨b,rows,fee⟩:=paid
  let D:=fun i=>(Q.reg i).support
  let mode:ℕ→Finset (Site n):=fun i=>{(Q.reg i).site}
  let α:=p.supportExponent-1
  have rp:Rooted mode D p.B (α+1) b δ:=by
    intro x
    convert fee x using 1
    funext i
    by_cases here:(Q.reg i).site=x <;>
      simp [mode,D,here,Ne.symm,α,RG.BudgetPoint.mass,mul_comm]
  have close:=root_hit (o:=fun x:Site n=>x) (μ:=1) (a:=α) (M:=p.B)
      (Occupancy.of_injective Function.injective_id) (fun i=>(rows i).1) (budget_nonneg (fee 0))
      (fun i _=>⟨(Q.reg i).site,mem_singleton_self _,(Q.reg i).anchor⟩) rp
  simp only [Nat.cast_one,one_mul] at close
  exact ⟨b,rows,fee,close⟩

theorem hit_slice_rows {δ:ℝ}(paid:Q.EBound p δ)(margin:1≤p.supportExponent)
    (X:Support n)(cut:ℕ)(test:ℕ→Config G n):
    SumBudget (fun i=>‖sliceRow Q p X cut i (test i)‖) (sliceFare p X cut δ):=by
  obtain ⟨b,rows,_,close⟩:=vacuum_hit_credit Q p paid
  let D:=fun i=>(Q.reg i).support
  let α:=p.supportExponent-1
  let C:=siteFactor p.B*δ
  let fee':=fun x (i:ℕ)=>if x∈D i then b i*Real.exp (α*coverNumber p.B (D i)) else 0
  have total:=budget_over X fee' (fun _=>C) (fun x _=>close x)
  rw [sum_const,nsmul_eq_mul] at total
  let c:=Real.exp (-α*(cut:ℝ))
  apply budget_mono (budget_scale (Real.exp_pos _).le total) (fun i=>norm_nonneg _)
  intro i
  by_cases used:incident Q p X cut i
  · obtain ⟨⟨x,hx,orig⟩,far⟩:=used
    have own:fee' x i ≤ ∑z∈X,fee' z i:=single_le_sum (fun z _=>(close z).1 i) hx
    have unweighted:‖Q.regularOccurrence p i (test i)‖≤b i:=by
      by_cases clear:Healthy p.threshold (D i) (test i)
      · rw [Activities.regularOccurrence,masked_eq _ _ _ _ clear]
        exact (rows i).2 (test i) clear [] (Nat.zero_le _) (by simp)
      rw [Activities.regularOccurrence,masked_ne _ _ _ _ clear,norm_zero]
      exact (rows i).1
    have one:1≤c*Real.exp (α*coverNumber p.B (D i)):=by
      dsimp only [c]
      rw [←Real.exp_add,Real.one_le_exp_iff]
      have nonneg:0≤α:=sub_nonneg.mpr margin
      have long:(cut:ℝ)≤coverNumber p.B (D i):=by exact_mod_cast far
      nlinarith only [mul_le_mul_of_nonneg_left long nonneg]
    rw [sliceRow,if_pos ⟨⟨x,hx,orig⟩,far⟩]
    refine unweighted.trans ((le_mul_of_one_le_left (rows i).1 one).trans ?_)
    calc _ = c*fee' x i:=by simp [fee',show x∈D i from orig];ring
         _ ≤ _:=mul_le_mul_of_nonneg_left own (Real.exp_pos _).le
  rw [sliceRow,if_neg used,norm_zero]
  exact mul_nonneg (Real.exp_pos _).le (total.1 i)

theorem hit_slice_log {δ:ℝ}(paid:Q.EBound p δ)(reg:Q.RegularFamily p)(margin:1≤p.supportExponent)
    (X:Support n)(cut:ℕ):Measurable (sliceLog Q p X cut) ∧ ∀U,‖sliceLog Q p X cut U‖≤sliceFare p X cut δ:=by
  refine ⟨Measurable.tsum (fun i=>?_),fun U=>?_⟩
  · change Measurable (fun U : Config G n=>if incident Q p X cut i then Q.regularOccurrence p i U else (0:ℝ))
    by_cases used:incident Q p X cut i
    · simpa only [if_pos used,Activities.regularOccurrence] using
        (masked_measurable p.threshold (Q.reg i).support (Q.E i) (reg.smooth i).borel)
    simpa only [if_neg used] using (measurable_const:Measurable (fun _:Config G n=>(0:ℝ)))
  have fee:=hit_slice_rows Q p paid margin X cut (fun _=>U)
  exact (norm_tsum_le_tsum_norm fee.2.1).trans fee.2.2

end YM.Integration.FVA1Physical.Marked.Inherited
