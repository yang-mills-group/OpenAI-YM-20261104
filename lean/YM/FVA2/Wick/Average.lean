import YM.FVA2.Wick.Words
/-! # Identify the remaining (commuting) lattice Wick evaluation with RG10 GaussianScore
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Wick.Boson
open Function Set Finset Filter MeasureTheory
open MS MS.Koszul MS.Plane MS.Orbit MS.Orbit.Cog MS.Swirl MS.Book Convolve MS.Cylinder Taylor
open FormalOPE.RG10.MultiGauge
open PertExtension.Series.Radial PertExtension.GaussianScore
open scoped BigOperators Topology ContDiff Matrix
variable {E A B J : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable (e : Module.Basis A ℝ E) [Fintype A] [Fintype J]
local notation "p" => sector (A:=A) (J:=J)
local infixl:70 " ⋆ " => product p
local notation "σ" => Poly.encode (J:=J) e
local notation "T" => Permit E

abbrev atoms (e : Module.Basis A ℝ E) := Set.range (fun j => (coord e j).val)
omit [FiniteDimensional ℝ E] in
lemma paper_atoms (x:T) : x.val ∈ Submodule.span ℝ (↑(Submonoid.closure (atoms e))) := by
  rw [← Algebra.adjoin_eq_span]
  suffices hh : papers E ≤ Algebra.adjoin ℝ (atoms e) from hh x.property
  apply Algebra.adjoin_le
  rintro y ⟨l,rfl⟩
  classical
  let f : A→E→ℝ := fun j=>(coord e j).val
  have h : (l:E→ℝ)=∑ j:A,l (e j) • f j:= by
    funext i; conv_lhs=> arg 2; rw [← e.sum_repr i] -- inspect arg idx
    rw [map_sum,Finset.sum_apply]; refine Finset.sum_congr rfl (fun j _=>?_); rw [map_smul]; exact mul_comm ..
  change (l:E→ℝ) ∈ Algebra.adjoin ℝ (atoms e); rw [h]; exact (Algebra.adjoin ℝ _).sum_mem fun i _=> (Algebra.adjoin ℝ (atoms e)).smul_mem (Algebra.subset_adjoin ⟨i,rfl⟩) _
omit [FiniteDimensional ℝ E] [Fintype A] in
lemma monomial (x:E→ℝ)(h:x∈ Submonoid.closure (atoms e)) : ∃ n, ∃ f:Fin n→A,x=(cost e f Finset.univ).val := by
  apply Submonoid.closure_induction_left (motive:= fun x _ => ∃ n,∃ f:Fin n→A,x=(cost e f Finset.univ).val) _ _ h
  · refine ⟨0,Fin.elim0,?_⟩; rw [cost, Finset.univ_eq_empty, Finset.prod_empty]; rfl
  rintro x ⟨l,rfl⟩ y hy ⟨n,f,rfl⟩
  refine ⟨n+1,Fin.cons l f,?_⟩
  unfold cost; rw [Fin.prod_univ_succ]; simp
variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E)[Measure.IsAddHaarMeasure μ]
variable (b : Law E)
local notation "Q" => bosonMatrix b e
local notation "M" => Fermion.bev Q J
local notation "Ω" => Papers.opening μ b
lemma every (x:T) : View M (σ x)= (Ω x:ℂ) := by
  let L : Permit E→ₗ[ℝ] ℂ := (View M).restrictScalars ℝ ∘ₗ σ - Complex.ofRealCLM.toLinearMap ∘ₗ Ω
  let P (f:E→ℝ) := ∃ x:Permit E,x.val=f ∧ L x=0
  have hl (w:E→ℝ)(hi:w∈ Submodule.span ℝ (↑(Submonoid.closure (atoms e)))) : P w := by
    induction hi using Submodule.span_induction with
    | mem v h=>
      obtain ⟨l,f,rfl⟩ := monomial e v h
      refine ⟨ cost e f Finset.univ,rfl,?_⟩; exact sub_eq_zero.mpr (balance (J:=J) e f Finset.univ μ b) -- L unfolds
    | zero => exact ⟨0,rfl,map_zero L⟩
    | add => rename_i y v a l ia il; obtain ⟨y,rfl,ha⟩:=ia; obtain ⟨v,rfl,h⟩:=il; exact ⟨ y+v,rfl,by rw [map_add,ha,h,add_zero]⟩
    | smul => rename_i y u a l; obtain ⟨v,rfl,h⟩:=l; exact ⟨_,(show (y • v).val= y • v.val from rfl), by rw [map_smul,h,smul_zero]⟩
  obtain ⟨q,h,H⟩:=hl x.val (paper_atoms e x); exact sub_eq_zero.mp ((Subtype.ext h : q=x) ▸ H : L x=0)
end YM.FVA2.Wick.Boson
