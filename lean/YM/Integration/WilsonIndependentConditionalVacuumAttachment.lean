import YM.Integration.WilsonIndependentConditionalCoverBirth

/-! An intensive original unmarked coefficient uses a retained slot as a
front exactly when its angular rank is positive. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentConditionalVacuumAttachment
open Function RegulatorIR RegulatorIR.Budget RegulatorIR.Budget.Packet RegulatorIR.Diagram
open Lattice Laurent Bloch Matrix WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Soil
open scoped Classical BigOperators
variable {α:Type}[Fintype α]{r i j:ℕ}
variable {K:ropes Cover α α}{G:(n:Side)→ ropes (Site n) α α}
variable {T U:Gen ℝ (Cloth α)}{A B:(n:Side)→ Gen ℝ (Co n α)}

omit [Fintype α] in
theorem untouched (F:canal Cover α α ℝ 2 r)(hr:0<r):worn F=ruins F:=by
  funext x
  apply tsum_congr;intro y
  simp [tie,show r≠0 by omega]

theorem row {F:canal Cover α α ℝ 2 r}{J:berth α α ℝ 2 r}(h:Tremor J F)(hr:0<r)(x:dock Cover α r):
    Summable (F x):=by
  obtain ⟨s,A,hs,hA⟩:=h.covers
  have hit:Summable (tie F x):=(tie_cost hA hs le_rfl x).2.1.of_norm
  exact hit.congr (fun y=>by simp [tie,show r≠0 by omega])

theorem averaged {F:canal Cover α α ℝ 2 r}{J:berth α α ℝ 2 r}(h:Tremor J F)(hr:0<r):
    worn (Bank.swivel F)=Packet.symmetry (ruins F):=by
  rw [untouched _ hr]
  funext x;rw [symmetry_at];unfold Bank.swivel ruins
  simp only [Pi.smul_apply,Finset.sum_apply,smul_eq_mul]
  rw [tsum_mul_left]
  congr 1
  apply Summable.tsum_finsetSum
  exact fun v _=>row h hr (x∘v)

theorem joined (hc:Pilots G K)(ht:Yields (fun n=>A n (i+1)) (T (i+1)))
    (hu:Yields (fun n=>B n (j+1)) (U (j+1)))(g:i+j=r)(hr:0<r):
    worn (Bank.swivel (rill K T U r i j))=(1/2:ℝ) • matchTwo K T U r (i,j):=by
  subst r
  have h:=branch_point hc ht hu (rfl:i+j=i+j)
  have joint:ruins (rill K T U (i+j) i j)=
    WilsonIndependentConditionalCoverKnot.weight i j • knot K (T (i+1)) (U (j+1)):=by
    funext x;exact WilsonIndependentConditionalCoverKnot.raw K T U x (row h hr x)
  rw [averaged h hr,joint]
  unfold matchTwo
  split
  · funext x
    change Packet.symmetry _ x=(1/2:ℝ)*((((i:ℝ)+1)*((j:ℝ)+1))*Packet.symmetry _ x)
    rw [symmetry_at,symmetry_at]
    simp only [Pi.smul_apply,smul_eq_mul]
    rw [←Finset.mul_sum]
    unfold WilsonIndependentConditionalCoverKnot.weight
    push_cast;ring
  · rename_i hn;exact (hn rfl).elim

theorem original (hc:Pilots G K)(ht:∀i,Yields (fun n=>A n i) (T i))
    (hu:∀i,Yields (fun n=>B n i) (U i))(hr:0<r):
    whittle K T U r=(1/2:ℝ) • force K T U r:=by
  unfold whittle force;rw [Finset.smul_sum]
  apply Finset.sum_congr rfl;intro q h
  exact joined hc (ht _) (hu _) (Finset.HasAntidiagonal.mem_antidiagonal.mp h) hr

end YM.Integration.WilsonIndependentConditionalVacuumAttachment
