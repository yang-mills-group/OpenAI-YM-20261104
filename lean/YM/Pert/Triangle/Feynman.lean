import YM.Pert.Triangle.VertexLinear
/-! Extend the separated Wick matchings to arbitrary linear shell symbols before summing any composite labels. -/
set_option autoImplicit false
set_option maxHeartbeats 280000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Pert.Triangle.Receipt
open Maxwell Wick Function Set Classical Topology Finset Next.Rank.Normal
variable {G:Gauge} {J:Type} [Fintype J] (loc:J→Fin 3) (g:J→ℕ) (x:Points 3) (hx:x∈conf 3)
variable (L : (j:J)→ Probe G (g j)) (j:J)
lemma probe_by_components (i:ℕ) (A : Probe G i) : A= ∑ s:Fin (legDim G i), A (frame G i s) • coordinateLeg ⟨i,s⟩ := by
  apply (frame G i).ext
  intro k
  simp [coordinateLeg,Eq.comm]
include hx
private def Claim := draw loc g L x = sumTours loc g L x
private lemma expansion (s:Finset J) :
    ∀ L : (j:J)→Probe G (g j), (∀ i ∉ s, ∃ k, L i=coordinateLeg ⟨g i,k⟩) → Claim loc g x L := by
  induction s using Finset.induction_on with
  | empty =>
    intro L h
    choose f hf using (show ∀ i,∃ k,L i= coordinateLeg ⟨g i,k⟩ from fun i=>h i (Finset.notMem_empty _))
    exact tour_base loc g L x hx hf
  | @insert i t h ih =>
    intro L hb
    obtain ⟨M,hM⟩:=toursLinear loc g x hx L i
    let N := drawMap loc g x L i
    have hN (w): N w= draw loc g (update L i w) x := draw_eval ..
    let A (v : Fin (legDim G (g i))) := coordinateLeg (⟨g i,v⟩ : Slot G)
    have he (v) := ih (update L i (A v)) (fun k hk=> by
      by_cases Hk : k=i
      · subst k; exact ⟨v,(update_self ..)⟩
      rw [update_of_ne Hk]; exact hb k (by simp [Hk,hk]))
    have e (v): N (A v)=M (A v) := (hN (A v)).trans ((he v).trans (hM (A v)).symm)
    have claimed (p:Probe G (g i)) : Claim loc g x (update L i p) := by
      rw [Claim,← hN,← hM]
      nth_rw 1 [probe_by_components (g i) p]
      conv_rhs => rw [probe_by_components (g i) p]
      rw [_root_.map_sum,_root_.map_sum]
      exact Finset.sum_congr rfl fun v _ => by rw [LinearMap.map_smul, LinearMap.map_smul, show coordinateLeg _= A v from rfl,e]
    rw [show L=update L i (L i) from by ext j; by_cases e:j=i;subst j;simp; rw [update_of_ne e]]
    exact claimed ..

theorem register_eq : draw loc g L x = sumTours loc g L x := expansion loc g x hx univ L (by simp)
theorem killRegister (hh:∀ Q:Equiv.Perm J, Trace loc univ Q →
    ∃ a:J, loc a < loc (Q a) ∧ legKernel (L a) (L (Q a)) (x (loc a)-x (loc (Q a)))=0) :
    Wick.moment G x (block loc g L)=0 :=
   (register_eq loc g x hx L).trans <| Finset.sum_eq_zero fun Q h=>
   let ⟨a,hu,hv⟩:=hh Q ((Finset.mem_filter.mp h).2)
   Finset.prod_eq_zero (mem_filter.mpr ⟨Finset.mem_univ a,hu⟩) (by
             change (Complex.ofReal (legKernel (L a) (L (Q a)) (x (loc a)-x (loc (Q a)))))=0
             rw [hv,Complex.ofReal_zero])
end YM.Pert.Triangle.Receipt
