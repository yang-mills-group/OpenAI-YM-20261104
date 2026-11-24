import YM.Integration.FVA1Physical.Round2.FiniteGaugeMass
import YM.OPE.Thorn.Components
import YM.OPE.Therm.Bath
import YM.Push.ABSOLUTE_SUMS.Animals
import YM.Work.E08

/-! A single site gauge makes an arbitrarily dispersed finite collection of tested bonds
small. Its plaquette and cardinality costs depend only on the number of tests. -/
set_option autoImplicit false
set_option maxHeartbeats 850000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Set Finset Lattice RG YM.Wilson OPE.Therm Push.AbsoluteSums.Animals
open YM.Integration.FVA1Physical.Round2.Curvature
open scoped Classical BigOperators
variable {G:Gauge} {n:Side}

def sparseFaces (B:Finset (Edge (Site n))) (k:ℕ) : Finset (Face (Per n)) :=
  (ends B).biUnion (fun o=>neighbors (2*k+1) o ×ˢ (Finset.univ:Finset PlaqAxes))

def sparseLoss (k:ℕ) : ℝ := 16*(2*((2*k+1:ℕ):ℝ)+1)^5*(Fintype.card PlaqAxes:ℝ)
def sparseCount (k:ℕ) : ℕ := (2*k)*(ballCost (2*k+1)*Fintype.card PlaqAxes)

theorem sparse_count (B:Finset (Edge (Site n))) (k:ℕ) (size:B.card≤k) : (sparseFaces B k).card ≤ sparseCount k := by
  apply (card_biUnion_le (s:=ends B)).trans
  calc
    _ ≤ ∑ _o∈ends B,ballCost (2*k+1)*Fintype.card PlaqAxes := by
      apply sum_le_sum;intro o ho
      rw [card_product,card_univ];exact Nat.mul_le_mul_right _ (neighbors_card ..)
    _ = (ends B).card*(ballCost (2*k+1)*Fintype.card PlaqAxes) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ ((ends_card B).trans (Nat.mul_le_mul_left 2 size))

theorem sparse_axial (B:Finset (Edge (Site n))) (k:ℕ) (size:B.card≤k) (period:2*(2*k+1)<n.val)
    (U:Config G n) {q:ℝ} (nonneg:0≤q) (good:U∈House.chilly (sparseFaces B k) q) :
    ∃ z:Site n→G.El,∀ e∈B,G.chord (gauge z U e) ≤ sparseLoss k*q := by
  let D:=ends B
  let E:SimpleGraph (↥D):=SimpleGraph.mk (fun i j=>i≠j ∧ separation i.val j.val ≤ 1)
    ⟨fun i j e=>⟨e.1.symm,separation_comm i.val j.val ▸ e.2⟩⟩ ⟨fun i h=>h.1 rfl⟩
  let eq:Setoid (↥D):=⟨E.Reachable,E.reachable_is_equivalence⟩
  let C:=Quotient eq
  let cl:↥D→C:=Quotient.mk''
  have surj:Surjective cl:=@Quotient.mk_surjective _ eq
  let rep (c:C):↥D:=(surj c).choose
  have fiber (c:C):cl (rep c)=c:=(surj c).choose_spec
  have classes (i j:↥D):E.Reachable i j ↔ cl i=cl j:=(@Quotient.eq' _ eq i j).symm
  have diam (i:↥D):separation (rep (cl i)).val i.val ≤ 2*k := by
    have H:=OPE.Thorn.length_bound E (fun x:↥D=>x.val) 1 (fun h=>h.2)
      ((classes ..).2 (fiber (cl i)))
    simpa only [one_mul,Fintype.card_coe] using H.trans (by
      rw [one_mul,Fintype.card_coe];exact (ends_card B).trans (Nat.mul_le_mul_left 2 size))
  have cover (c:C):∃ a:Site n→G.El,∀ e:Edge (Site n),separation (rep c).val e.1 ≤ 2*k →
      G.chord (gauge a U e) ≤ sparseLoss k*q := by
    apply Work.E08.axial_patch (rep c).val U (2*k) (2*k+1) le_rfl period q nonneg
    intro y hy h
    apply good (y,h)
    exact mem_biUnion.mpr ⟨(rep c).val,(rep c).property,
      mem_product.mpr ⟨(neighbors_mem ..).mpr hy,mem_univ _⟩⟩
  let ax (c:C):Site n→G.El:=(cover c).choose
  let z (i:Site n):G.El:=if hi:i∈D then ax (cl ⟨i,hi⟩) i else 1
  refine ⟨z,?_⟩
  intro e he
  have h0:e.1∈D:=mem_union_left _ (mem_image_of_mem Prod.fst he)
  have h1:e.1+step e.2∈D:=mem_union_right _ (mem_image_of_mem (fun b:Edge (Site n)=>b.1+step b.2) he)
  let i:↥D:=⟨e.1,h0⟩;let j:↥D:=⟨e.1+step e.2,h1⟩
  have near:separation i.val j.val≤1:=by
    change separation e.1 (e.1+step e.2)≤1
    rw [separation_comm, separation,add_comm,add_sub_cancel_right];exact pdist_step _
  have eqc:cl i=cl j:=by
    by_cases same:i=j
    · exact congrArg cl same
    apply (classes i j).1
    exact (show E.Adj i j from ⟨same,near⟩).reachable
  have hl:z e.1=ax (cl i) e.1:=dif_pos h0
  have hr:z (e.1+step e.2)=ax (cl i) (e.1+step e.2):=by rw [eqc];exact dif_pos h1
  have id:gauge z U e=gauge (ax (cl i)) U e:=by unfold Lattice.gauge;rw [hl,hr]
  rw [id]
  exact (cover (cl i)).choose_spec e (diam i)

end YM.Integration.FVA1Physical.Wilson
