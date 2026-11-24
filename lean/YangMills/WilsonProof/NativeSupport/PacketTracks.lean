import YangMills.WilsonProof.NativeSupport.RelocatedPattern
import YangMills.WilsonProof.NativeSupport.PackedEndpoint
import YangMills.WilsonProof.NativeSupport.JointCoatLocality

/-! The marked location may move inside a larger support while the gauge
field in the word stays at its original location. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.InletSusceptibility.Packet
open Function Finset Lattice RG Wilson RGComparison.Core16
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {B : Type*}

def track {A : Levels G} {p N : ℕ} (T : Slices A p)
    (x : Site (A.S.side N p)) (j : ℕ) : Site (A.S.side j p) :=
  if h : j ≤ N then home (traversal T h) x else 0

theorem track_end {A : Levels G} {p N : ℕ} (T : Slices A p)
    (x : Site (A.S.side N p)) : track T x N=x := by simp [track,home]

theorem track_step {A : Levels G} {p N : ℕ} (T : Slices A p)
    (x : Site (A.S.side N p)) {j : ℕ} (hj : j<N) :
    (A.clock.op j p).ratio.parent (track T x (j+1))=track T x j := by
  rw [track,dif_pos (show j+1≤N from hj),track,dif_pos hj.le,traversal_push T hj]; rfl

theorem track_move {A : Levels G} {p k N : ℕ} (T : Slices A p) (hk : k ≤ N)
    (x : Site (A.S.side N p)) (b : Site (A.S.side k p)) :
    track T (liftSite (traversal T hk) b+x) k=b+home (traversal T hk) x := by
  rw [track,dif_pos hk,ancestor_move]

theorem translate_invariant {F : Config G n→B} (h : GaugeInvariant F) (b : Site n) :
    GaugeInvariant (fun U=>F (pull 1 b U)) := by
  intro t U
  simp only [pull_one]
  have moved : Lattice.translate b (Lattice.gauge t U)=
      Lattice.gauge (fun x=>t (x+b)) (Lattice.translate b U) := by
    funext e; simp [Lattice.translate,Lattice.gauge,add_right_comm]
  exact (congrArg F moved).trans (h _ _)

theorem ball_local {F : Config G n→B} {a x : Site n} {s k : ℕ}
    (h : LocalOn (halo s {a}) F) (bill : separation x a ≤ k) (b : Site n) :
    LocalOn (halo (s+k) {b+x}) (fun U=>F (pull 1 b U)) := by
  have moved {y : Site n} (hy : y∈halo s {a}) : y+b∈halo (s+k) {b+x} := by
    obtain ⟨v,hv,dis⟩:=halo_spec.mp hy
    have ev := mem_singleton.mp hv
    subst v
    refine halo_spec.mpr ⟨b+x,mem_singleton_self _,?_⟩
    change pdist (b+x-(y+b)) ≤ _
    rw [show b+x-(y+b)=x-y by abel]
    exact (separation_triangle x a y).trans ((Nat.add_le_add bill dis).trans_eq (Nat.add_comm ..))
  intro U Z agree
  simp only [pull_one]; apply h
  intro e hstart hstop
  refine agree (e.1+b,e.2) (moved hstart) ?_
  change e.1+b+step e.2∈halo (s+k) {b+x}
  rw [add_right_comm]
  exact moved hstop

theorem ball_cover (P : BudgetPoint) (x : Site n) (s : ℕ) :
    coverNumber P.B (halo s {x}) ≤ (2*s+1)^4 := by
  have sub : halo s {x}⊆halo (s*P.B) {x} := by
    intro y hy
    obtain ⟨z,hz,h⟩:=halo_spec.mp hy
    exact halo_spec.mpr ⟨z,hz,h.trans (Nat.le_mul_of_pos_right _ P.B_pos)⟩
  simpa only [two_mul] using (Corona.cover_mono sub P.B).trans (Corona.tile x s P.B P.B_pos)

end YM.Integration.InletSusceptibility.Packet
