import YM.Integration.WilsonIndependentConditionalSwappedBirth

/-! The complete conditional product term on the measured bulk Markov step,
before a child is averaged and before its scalar is taken. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentConditionalCoverDrift
open RegulatorIR RegulatorIR.Budget RegulatorIR.Diagram WilsonCoeffUV WilsonCoeffUV.Blue
open WilsonCoeffUV.Bank WilsonCoeffUV.Soil Lattice Laurent Bloch Matrix
open scoped Classical BigOperators
variable {α:Type}[Fintype α]{p:Cover}{r k e:ℕ}
variable {K:ropes Cover α α}{G:(n:Side)→ ropes (Site n) α α}
variable {V W:Layers ℝ (Cloth α)}{A Y:(n:Side)→ Layers ℝ (Co n α)}

theorem turn {T U:Gen ℝ (Cloth α)}{A Y:(n:Side)→ Gen ℝ (Co n α)}
    (fund:Pilots G K)(ht:∀i,Yields (fun n=>A n i) (T i))
    (hu:∀i,Bends p (fun n=>Y n i) (U i))(r:ℕ):
    force K T U r=force K.transpose U T r:=by
  unfold force
  calc
    _ = ∑ q∈Finset.HasAntidiagonal.antidiagonal r,matchTwo K.transpose U T r q.swap:=by
      apply Finset.sum_congr rfl;intro q h
      exact WilsonIndependentConditionalSwappedBirth.aligned fund (ht _) (hu _) (Finset.HasAntidiagonal.mem_antidiagonal.mp h)
    _=_:=Finset.Nat.sum_antidiagonal_swap

theorem raised (fund:Pilots G K)(Ksym:K.transpose=K)
    (grain:∀i≤k,∀j≤e,∀r,Yields (fun n=>A n i j r) (V i j r))
    (source:∀i≤k,∀j≤e,∀r,Bends p (fun n=>Y n i j r) (W i j r))(r:ℕ):
    paintC K V W k e r=(1/2:ℝ) • Diagram.drift K W V k e r:=by
  unfold paintC Diagram.drift Diagram.carry
  simp only [Finset.sum_apply,Finset.smul_sum]
  calc
    _=∑ a∈Finset.HasAntidiagonal.antidiagonal k,∑ j∈Finset.HasAntidiagonal.antidiagonal e,
         (1/2:ℝ) • force K (W a.2 j.2) (V a.1 j.1) r:=by
      apply Finset.sum_congr rfl;intro a ha;apply Finset.sum_congr rfl;intro j hj
      have a':a.1+a.2=k:=Finset.HasAntidiagonal.mem_antidiagonal.mp ha
      have j':j.1+j.2=e:=Finset.HasAntidiagonal.mem_antidiagonal.mp hj
      have hh:=grain a.1 (by omega) j.1 (by omega)
      have hv:=source a.2 (by omega) j.2 (by omega)
      rw [WilsonIndependentConditionalCoverBirth.original fund (fun _ _=>hh _) (fun _ _=>hv _),
        turn fund hh hv r,Ksym]
    _ = ∑ a∈Finset.HasAntidiagonal.antidiagonal k,∑ j∈Finset.HasAntidiagonal.antidiagonal e,
         (1/2:ℝ) • force K (W a.2 j.1) (V a.1 j.2) r:=by
      apply Finset.sum_congr rfl;intro a _
      exact Finset.Nat.sum_antidiagonal_swap (f:=fun j=>(1/2:ℝ) • force K (W a.2 j.1) (V a.1 j.2) r)
    _=_:=Finset.Nat.sum_antidiagonal_swap (f:=fun a=>∑ j∈Finset.HasAntidiagonal.antidiagonal e,
      (1/2:ℝ) • force K (W a.1 j.1) (V a.2 j.2) r)

theorem original (fund:Pilots G K)(Ksym:K.transpose=K)
    (grain:∀i≤k,∀j≤e,∀r,Yields (fun n=>A n i j r) (V i j r))
    (source:∀i≤k,∀j≤e,∀r,Bends p (fun n=>Y n i j r) (W i j r))(r:ℕ):
    paintC K V W k e r + paintC K.transpose V W k e r=Diagram.drift K W V k e r:=by
  rw [Ksym,raised fund Ksym grain source,←add_smul]
  norm_num

end YM.Integration.WilsonIndependentConditionalCoverDrift
