import YM.LocalLTE.Venue.Venetian
/-! # Following reallocations with live soft terms. -/
set_option autoImplicit false
noncomputable section
namespace YM.Merge.Motion
open Function Filter Set Lattice Wilson RG Ovens Ovens.Pipes MeasureTheory Work.H03
open Pressure Progress.DirectedRecipe Rack ConnectedActivityE6 Finset Push Push.AbsoluteSums
open PhysicalNext.Repeat Mallow Daisy Switch
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {ι:Type}[Fintype ι] {G : Gauge}{n : Side}
    {X:Pipes G n} {d:Tap G n} {P : BudgetPoint} {r c δ A B κ γ w v a:ℝ} {o : Site n}
set_option quotPrecheck false
variable (P) (F:ℕ≃ Pellet X)(ha:HasSlots P (X.pours d))
variable (d) (K Z: ℝ→Finset ι→ Code G n) (h:Pays (X.pours d) P K B (P.supportExponent+1))
    (ht:Smoke X P Z w)(he:Payments.Rates P.B A B w κ)
abbrev sailX (x V):= stuff (arrange P F) (solid F P (alt (d:=d) (K x V) (Z x V)))
local notation "k"=> sailX d P F K Z -- argument order? variable (d) inserted pre-P probably
include ht h ha
lemma games (V:Config G n)(x p)(hp:x∈ Set.Icc (0:ℝ) 1):
    (black (X.pours d) (sailX d P F K Z x p)).gas P V = (black (X.pours d) (K x p)).gas P V * Real.exp (∑' i,Z x p i V):=by
    have hz:= adjusts P F ha (Z x p) (K x p); exact (congr_fun hz.same_gas _).trans ((Passage.gathered (F:=F) (firesL d h ht x hp p) V).tsum_eq)
include he
lemma blazeP : Pays (X.pours d) P (sailX d P F K Z) A P.supportExponent:=by
    have hp:= harvestU d h ht he F; let t:=arrange P F; let f x j:= alt (d:=d) (K x j) (Z x j)
    have hv(x j):=adjusts P F ha (Z x j) (K x j)
    obtain ⟨a,ha',hA⟩:=hp.bought; have hT: (X.pours d).ForcedFamily P:=by
        have hu:=h.licensed 0 ∅ (show 0∈Set.Icc (0:ℝ) 1 from ⟨le_rfl,zero_le_one⟩)
        rw [h.term] at hu; exact hu
    constructor
    · intro j; funext i; by_cases hh:i∈ Set.range t
      · obtain ⟨u,rfl⟩:=hh; unfold sailX; unfold t; rw [stuffed,h.term, ht.off]; exact once P F ha hT u
      exact (blank _ _ hh).trans (unusedG P F ha i hh).symm
    · intro x j hx; exact (hv x j).forced_family (hp.licensed x j hx) hT.symtest hT.meas_test hT.reads_test
    refine ⟨stuff t a,fun i=>?_,fun i=>transfer_budget t ?_ ?_ (hA i)⟩
    · by_cases he:i∈Set.range t
      · obtain ⟨u,rfl⟩:=he; unfold t; simp_rw [sailX,stuffed]; exact ha' u
      rw [blank _ _ he]; unfold t at he; simp_rw [sailX,blank _ _ he]; exact paidZero (ι:=ι) (U:=Config G n)
    · intro i'; simp only [stuffed,pours,fused]; change (if _ then a i'*Real.exp (P.supportExponent * coverNumber P.B (X.kernel (t i')).support) else (0:ℝ))= _
      rw [show (X.kernel (t i')).support = (addr F P i').support from congr_arg Foot.support (locale P F ha i')]
    intro j hj; split; rw [blank _ _ hj,zero_mul]; rfl
omit ht h he
omit [Fintype ι] in
lemma strands (i:ι)(o:Site n)(hh:Hush i o (fun i=>(X.kernel i).support) K)(hZ:Hush i o X.softer Z): Hush i o (fun i=>(X.kernel i).support) (sailX d P F K Z):=by
    intro j x p hx; by_cases he:j∈ Set.range (arrange P F)
    · obtain ⟨l,rfl⟩:=he; unfold sailX; rw [stuffed,stuffed]; funext U; unfold solid; split; swap; · rfl
      apply Finset.prod_congr rfl; intro y hy; have hz:o∉X.patch y:= by
         intro hp; apply hx; change o ∈ (X.kernel (arrange P F l)).support; rw [show (X.kernel (arrange P F l)).support= (addr F P l).support from congr_arg Foot.support (locale P F ha l)]; exact subset_biUnion_of_mem X.patch hy hp
      rcases y with a|a
      · exact congr_fun (hh a x p hz) U
      exact congr_arg (fun t:ℝ=> Real.exp t-1) (congr_fun (hZ a x p hz) U)
    unfold sailX; rw [blank _ _ he,blank _ _ he]
end YM.Merge.Motion
