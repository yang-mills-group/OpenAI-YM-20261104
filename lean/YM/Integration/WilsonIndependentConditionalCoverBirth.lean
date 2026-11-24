import YM.Integration.WilsonIndependentConditionalCoverKnot

/-! A genuinely new marked/vacuum connection before summing a child.
All its spatial income is taken from its own period families. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentConditionalCoverBirth
open Function RegulatorIR RegulatorIR.Budget RegulatorIR.Budget.Packet RegulatorIR.Diagram
open Lattice Laurent Bloch Matrix WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Soil
open scoped Classical BigOperators
variable {α:Type}[Fintype α]{p:Cover}{r i j:ℕ}
variable {K:ropes Cover α α}{G:(n:Side)→ ropes (Site n) α α}
variable {T U:Gen ℝ (Cloth α)}{A B:(n:Side)→Gen ℝ (Co n α)}

theorem averaged {k:ℕ}{F:canal Cover α α ℝ 2 k}{J:berth α α ℝ 2 k}(h:Paves p J F):
    ruins (Bank.swivel F)=Packet.symmetry (ruins F):=by
  funext x;rw [symmetry_at];unfold Bank.swivel ruins
  simp only [Pi.smul_apply,Finset.sum_apply,smul_eq_mul]
  rw [tsum_mul_left]
  congr 1
  apply Summable.tsum_finsetSum
  exact fun v _=>WilsonIndependentConditionalCoverFare.original h (x∘v)

private theorem scale {X:Type}{s:ℕ}(c:ℝ)(F:Packet X s):Packet.symmetry (c • F)=c • Packet.symmetry F:=by
  funext x
  rw [symmetry_at,Pi.smul_apply,smul_eq_mul,symmetry_at]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [←Finset.mul_sum];ring

theorem joined (hc:Pilots G K)(ht:Yields (fun n=>A n (i+1)) (T (i+1)))
    (hu:Bends p (fun n=>B n (j+1)) (U (j+1)))(g:i+j=r):
    ruins (Bank.swivel (rill K T U r i j))=(1/2:ℝ) • matchTwo K T U r (i,j):=by
  subst r
  have h:=branch_read hc ht hu (show i+j=i+j from rfl)
  rw [averaged h,WilsonIndependentConditionalCoverKnot.original K T U p h,scale]
  unfold matchTwo
  split
  · change _=(1/2:ℝ) • ((((i:ℝ)+1)*((j:ℝ)+1)) • Packet.symmetry (knot K (T (i+1)) (U (j+1))))
    rw [smul_smul]
    congr 1
    simp [WilsonIndependentConditionalCoverKnot.weight,mul_assoc]
  · rename_i hne;exact (hne rfl).elim

theorem original (hc:Pilots G K)(ht:∀ i≤r,Yields (fun n=>A n (i+1)) (T (i+1)))
    (hu:∀ i≤r,Bends p (fun n=>B n (i+1)) (U (i+1))):
    rondel K T U r=(1/2:ℝ) • force K T U r:=by
  unfold rondel force;rw [Finset.smul_sum]
  apply Finset.sum_congr rfl;intro q h
  have g:q.1+q.2=r:=Finset.HasAntidiagonal.mem_antidiagonal.mp h
  exact joined hc (ht _ (by omega)) (hu _ (by omega)) g

end YM.Integration.WilsonIndependentConditionalCoverBirth
