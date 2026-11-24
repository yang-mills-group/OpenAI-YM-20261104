import YM.Integration.QLocalCompulsoryInventoryProduct
import YM.Integration.QLocalLaurentOrderTail

/-! Split an actual signed marked bank on the physical hot sites of each
row's own plot. One total root allowance pays the full thermal part even
when many sites are flagged simultaneously. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalThermalPacketDivision
open Function Finset Lattice Wilson RG Marker
open Comparison.Density.RenderM LocalComparison LocalComparison.MarkedPackets Push.AbsoluteSums
open scoped BigOperators Classical
variable {G:Gauge} {V:Type} [DecidableEq V] {Γ:Census V} {D:V → ComparisonDensity.Address.Orbit}
    {n:Side} (P:MarkedPackets D G n Γ) {q:BudgetPoint} {a:V→Support n}
    {region:Comparison.Density.Testing.Region (fun i=>(D i).Mood) n}
    {w:V→ℝ} {g width budget:ℝ} {off cov:ℕ}

def plot (i:ℕ) : Support n := (P.packet i).elim ∅ (fun T=>T.plot)

def first (S:Support n) : Option (Site n) :=
  if h:S.Nonempty then some h.choose else none

def pick (q:BudgetPoint) (U:Config G n) (i:ℕ) : Option (Site n) :=
  first (plot P i∩flags q.threshold U)

theorem picked {q:BudgetPoint} {U:Config G n} {i:ℕ} {ξ:Site n} (e:pick P q U i=some ξ) :
    ξ∈plot P i ∧ ξ∈flags q.threshold U := by
  unfold pick first at e
  split at e
  next h=>exact (Option.some.inj e) ▸ Finset.mem_inter.mp h.choose_spec
  contradiction

theorem healthy (q:BudgetPoint) (U:Config G n) (i:ℕ) :
    pick P q U i=none ↔ Healthy q.threshold (plot P i) U := by
  by_cases e:(plot P i∩flags q.threshold U).Nonempty
  · simp only [pick,first,dif_pos e,reduceCtorEq,false_iff]
    exact fun clean=>e.ne_empty (Finset.disjoint_iff_inter_eq_empty.mp clean)
  · simp only [pick,first,dif_neg e,true_iff]
    exact Finset.disjoint_iff_inter_eq_empty.mpr (Finset.not_nonempty_iff_eq_empty.mp e)

private theorem original {f:ℕ→Prop} {i:ℕ} {T:Token G n (fun v=>(D v).Mood) (P.rank i)}
    (H:(WilsonPrescribedPacketTail.slice P f).packet i=some T) : P.packet i=some T := by
  by_cases e:f i
  · simpa [WilsonPrescribedPacketTail.slice,e] using H
  · simp [WilsonPrescribedPacketTail.slice,e] at H

theorem clip (H:P.Paid q a region w g width budget off cov) (f:ℕ→Prop) :
    (WilsonPrescribedPacketTail.slice P f).Paid q a region w g width budget off cov := by
  refine
    { width_pos := H.width_pos
      positive := H.positive
      coefficient := fun i T e=>H.coefficient i T (original P e)
      paths := fun i T e=>H.paths i T (original P e)
      addresses := fun i T e=>H.addresses i T (original P e)
      symmetry := fun i T e=>H.symmetry i T (original P e)
      reads := fun i T e=>H.reads i T (original P e)
      multilinear := fun i T e=>H.multilinear i T (original P e)
      cover := fun i T e=>H.cover i T (original P e)
      width_reserved := H.width_reserved
      roots := ?_ }
  intro v
  apply budget_mono (H.roots v)
  · intro i
    by_cases keep:f i
    · cases e:P.packet i with
      | none => simp [WilsonPrescribedPacketTail.slice,keep,e]
      | some t => simpa [WilsonPrescribedPacketTail.slice,keep,e] using (H.roots v).1 i
    · simp [WilsonPrescribedPacketTail.slice,keep]
  · intro i
    by_cases keep:f i
    · cases e:P.packet i <;> simp [WilsonPrescribedPacketTail.slice,keep,e]
    · simpa [WilsonPrescribedPacketTail.slice,keep] using (H.roots v).1 i

variable [Fintype V]

def part (f:ℕ→Prop) (x:TestSpace D) (g:ℝ) (U:Config G n) : Poly Γ :=
  (WilsonPrescribedPacketTail.slice P f).read x g U

def flag (q:BudgetPoint) (x:TestSpace D) (g:ℝ) (ξ:Site n) (U:Config G n) : Poly Γ :=
  part P (fun i=>pick P q U i=some ξ) x g U

def clear (q:BudgetPoint) (x:TestSpace D) (g:ℝ) (U:Config G n) : Poly Γ :=
  part P (fun i=>pick P q U i=none) x g U

def dirty (q:BudgetPoint) (x:TestSpace D) (g:ℝ) (U:Config G n) : Poly Γ :=
  part P (fun i=>pick P q U i≠none) x g U

theorem quiet (q:BudgetPoint) (x:TestSpace D) (g:ℝ) (ξ:Site n) (U:Config G n) :
    (flag P q x g ξ U).part Γ.quiet=0 :=
  (WilsonPrescribedPacketTail.slice P _).quiet_read _ _ _

private def row (x:TestSpace D) (g:ℝ) (U:Config G n) (i:ℕ) := Poly.send (P.mode i) (P.term x g U i)

omit [Fintype V] in
private theorem term (f:ℕ→Prop) (x:TestSpace D) (g:ℝ) (U:Config G n) (i:ℕ) :
    row (WilsonPrescribedPacketTail.slice P f) x g U i=if f i then row P x g U i else 0 := by
  by_cases hf:f i
  · cases e:P.packet i <;> simp [row,MarkedPackets.term,WilsonPrescribedPacketTail.slice,hf,e]
  · simp [row,MarkedPackets.term,WilsonPrescribedPacketTail.slice,hf]

omit [Fintype V] in
private theorem payable (H:P.Paid q a region w g width budget off cov) (hg:g≠0)
    (f:ℕ→Prop) (x:TestSpace D) (U:Config G n) :
    Summable (row (WilsonPrescribedPacketTail.slice P f) x g U) :=
  NativePaidPacketColors.read_summable (clip P H f) hg x g U

theorem partition (phys:BudgetPoint) (H:P.Paid q a region w g width budget off cov) (hg:g≠0) (x:TestSpace D) (U:Config G n) :
    (∑ξ∈flags phys.threshold U,flag P phys x g ξ U)=dirty P phys x g U ∧
    clear P phys x g U+dirty P phys x g U=P.read x g U := by
  let s:=flags phys.threshold U
  constructor
  · change (∑ξ∈s,∑' i,row (WilsonPrescribedPacketTail.slice P (fun j=>pick P phys U j=some ξ)) x g U i)=
      ∑' i,row (WilsonPrescribedPacketTail.slice P (fun j=>pick P phys U j≠none)) x g U i
    rw [←Summable.tsum_finsetSum (fun ξ _=>payable P H hg (fun j=>pick P phys U j=some ξ) x U)]
    apply tsum_congr
    intro i
    simp_rw [term]
    cases e:pick P phys U i with
    | none=>simp
    | some ξ=>
      have hi:ξ∈s:=(picked P e).2
      simp [hi]
  · change (∑' i,row (WilsonPrescribedPacketTail.slice P (fun j=>pick P phys U j=none)) x g U i)+
      (∑' i,row (WilsonPrescribedPacketTail.slice P (fun j=>pick P phys U j≠none)) x g U i)=∑' i,row P x g U i
    rw [←(payable P H hg (fun j=>pick P phys U j=none) x U).tsum_add
      (payable P H hg (fun j=>pick P phys U j≠none) x U)]
    exact tsum_congr (fun i=>by by_cases he:pick P phys U i=none <;> simp [term,he])

/-- The entire signed sum is assessed once, independently of the number
of hot sites and without separating any exterior compulsory factors. -/
theorem joint (phys:BudgetPoint) (H:P.Paid q a region w g width budget off cov) (hg:g≠0)
    (cap:ℕ) (hc:P.rankCap≤cap) (x:IndependentTests D) (U:Config G n) :
    Poly.price w (∑ξ∈flags phys.threshold U,flag P phys (testInclusion D x) g ξ U)≤
      uniformReadCost cap (Fintype.card V) budget := by
  rw [(partition P phys H hg (testInclusion D x) U).1]
  exact ((clip P H _).uniform_read cap hc x U).2

end YM.Integration.QLocalThermalPacketDivision
