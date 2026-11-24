import YM.Integration.QLocalMarkedSpectator
import YM.Overlay.Table

/-! A signed increment rooted at each actual thermal flag is counted once
by the exact original compulsory inventory, on every admitted packet. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalCompulsoryInventoryProduct
open Function Finset Lattice Wilson RG Marker Overlay Extra.Trajectories
open scoped Classical BigOperators
variable {G:Gauge} {n:Side} {V:Type} [DecidableEq V] {Γ:Census V} {P:Rep G n}

def localCharge (P:Rep G n) (h:Site n → Config G n→Poly Γ) (i:ℕ) (U:Config G n) : Poly Γ :=
  ∑ ξ∈(P.activities.forced i).inventory,h ξ U

def total (P:Rep G n) (h:Site n → Config G n→Poly Γ) (U:Config G n) : Poly Γ :=
  ∑ ξ∈flags P.p.threshold U,h ξ U

private theorem quiet_sum {α:Type*} (l:Finset α) (h:α→Poly Γ) (hz:∀i∈l,(h i).part Γ.quiet=0) :
    (∑i∈l,h i).part Γ.quiet=0 := by
  rw [Poly.part_sum]
  exact Finset.sum_eq_zero hz

theorem local_quiet (h:Site n → Config G n→Poly Γ) (hz:∀ξ U,(h ξ U).part Γ.quiet=0)
    (i:ℕ) (U:Config G n) : (localCharge P h i U).part Γ.quiet=0 :=
  quiet_sum _ _ (fun ξ _=>hz ξ U)

theorem total_quiet (h:Site n → Config G n→Poly Γ) (hz:∀ξ U,(h ξ U).part Γ.quiet=0)
    (U:Config G n) : (total P h U).part Γ.quiet=0 :=
  quiet_sum _ _ (fun ξ _=>hz ξ U)

theorem exact_cover (h:Site n → Config G n→Poly Γ) (U:Config G n) (l:Finset ℕ)
    (ad:P.activities.admissible P.p U l) : ∑i∈l,localCharge P h i U=total P h U := by
  have dist:(l:Set ℕ).PairwiseDisjoint (fun i=>(P.activities.forced i).inventory) :=
    fun i hi j hj hn=>(ad.1 hi hj hn).mono (P.activities.forced i).inventory_sup (P.activities.forced j).inventory_sup
  unfold total localCharge
  rw [←ad.2,Finset.sum_biUnion dist]

variable [Fintype V]

private theorem exp_sum {α:Type*} (s:Finset α) (f:α→Poly Γ) (hz:∀i,(f i).part Γ.quiet=0) :
    Poly.pass (∑i∈s,f i)=∏i∈s,Poly.pass (f i) := by
  induction s using Finset.induction_on with
  | empty=>simp only [Finset.sum_empty,Finset.prod_empty,Extra.Trajectories.pass_zero]
  | @insert i s hi ih=>
    rw [Finset.sum_insert hi,Finset.prod_insert hi,pass_add (hz i) (quiet_sum s f (fun a _=>hz a)),ih]

def changed (a:Bands Γ P) (h:Site n → Config G n→Poly Γ) (i:ℕ) (U:Config G n) : Poly Γ :=
  Poly.pass (localCharge P h i U)*a.each i U

theorem packet (a b:Bands Γ P) (h:Site n → Config G n→Poly Γ) (hz:∀ξ U,(h ξ U).part Γ.quiet=0)
    (e:∀ i U,b.each i U=changed a h i U) (l:Finset ℕ) (U:Config G n) :
    b.packet l U=Poly.pass (total P h U)*a.packet l U := by
  by_cases ad:P.activities.admissible P.p U l
  · simp only [Bands.packet,if_pos ad,e,changed,Finset.prod_mul_distrib]
    rw [←exp_sum l (fun i=>localCharge P h i U) (fun i=>local_quiet h hz i U),
      exact_cover h U l ad]
  · simp only [Bands.packet,if_neg ad,mul_zero]

/-- The unit with signed inverse permits the exact reindex even before a
particular absolute exterior estimate is applied. -/
theorem cluster (a b:Bands Γ P) (h:Site n → Config G n→Poly Γ) (hz:∀ξ U,(h ξ U).part Γ.quiet=0)
    (e:∀ i U,b.each i U=changed a h i U) (U:Config G n) :
    b.cluster U=Poly.pass (total P h U)*a.cluster U := by
  letI : IsTopologicalSemiring (Poly Γ) :=
    { toContinuousAdd:=inferInstance,toContinuousMul:=inferInstance }
  let c:=total P h U
  have cq:c.part Γ.quiet=0:=total_quiet h hz U
  have iq:(-c).part Γ.quiet=0:=by rw [Poly.part_neg,cq,neg_zero]
  have inv:Poly.pass (-c)*Poly.pass c=1:=by
    rw [←pass_add iq cq,neg_add_cancel,Extra.Trajectories.pass_zero]
  unfold Bands.cluster
  simp_rw [packet a b h hz e]
  by_cases H:Summable (fun l=>a.packet l U)
  · exact H.tsum_mul_left _
  · have bad:¬Summable (fun l=>Poly.pass c*a.packet l U):=by
      intro Q
      apply H
      exact (Q.mul_left (Poly.pass (-c))).congr (fun l=>by rw [←mul_assoc,inv,one_mul])
    rw [tsum_eq_zero_of_not_summable bad,tsum_eq_zero_of_not_summable H,mul_zero]

theorem price (a b:Bands Γ P) (h:Site n → Config G n→Poly Γ) (hz:∀ξ U,(h ξ U).part Γ.quiet=0)
    (e:∀ i U,b.each i U=changed a h i U) (U:Config G n) {w:V→ℝ} (hw:∀i,0<w i)
    {δ:ℝ} (paid:Poly.price w (total P h U)≤δ) (small:δ≤1) :
    Poly.price w (b.cluster U-a.cluster U)≤2*δ*Poly.price w (a.cluster U) := by
  rw [cluster a b h hz e U,←sub_one_mul]
  exact (Poly.multiplication hw ..).trans (mul_le_mul_of_nonneg_right
    (QLocalMarkedSpectator.relative hw _ (total_quiet h hz U) paid small) (Poly.nonnegative hw _))

end YM.Integration.QLocalCompulsoryInventoryProduct
