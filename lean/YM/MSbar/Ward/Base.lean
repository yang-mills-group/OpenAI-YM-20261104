import YM.MSbar.Ward.Highest
/-! Compute ℏ^0 identity at tree boundary. Verify canonical at this grade (inputs). -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Play.Produce.Shield
open Dim Symbol Domain Diagram Scale Scale.Inertia Function Set Filter Category Counter Super Deck Work
open scoped Classical Topology BigOperators
variable {C:Type}{W:Edition C}{P Q:Vertex C}{X:Pulse W}{k i m:ℕ}{z:ℂ}(A:Shield X)
-- bare identity only, when actually at unscaled bar/disc. D profile equals canonical for
-- this germ. Later/classical data instantiate directly (no use of quantum perturbative identity).
def command (P:ℕ→Vertex C)(k:ℕ):= traceR W 0 A.R (P k)+(2:ℂ)⁻¹ • ∑ v∈Finset.antidiagonal k, traceT W 0 0 A.D (P v.1) (P v.2)
abbrev Roots (A:Shield X):= ∀ k,Flat (A.command X.seed k)
-- root difference relation
set_option maxHeartbeats 400000 in
lemma steady : flux A (evolve X) k 0 0 z=command A (fun i=> evolve X i 0 0 z) k:=by
    have H(i):Live W 0 (evolve X i 0 0 z):= (lands X i 0).besides _
    unfold flux command; simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply,seek,make,Finset.sum_apply,Finset.Nat.antidiagonal_zero,Finset.sum_singleton,tripped,Pi.zero_apply,sub_zero]
    have he: Play.spin A.R0 (evolve X k 0) 0 z=traceR W 0 A.R (evolve X k 0 0 z):=by
      unfold Play.spin Play.post R0; rw [arrows,plug_eq (H k), Parallel.sameR (H k) z 0]
    have hp (i j:ℕ): twin A.B0 (evolve X i 0 0) (evolve X j 0 0) z=traceT W 0 0 A.D (evolve X i 0 0 z) (evolve X j 0 0 z):=by unfold twin B0; rw [tree_val,plug_eq (H i),plug_eq (H j),Parallel.sameT (H i) (H j) z 0]
    simp_rw [he,hp]
lemma flat (ha:Roots A) (k:ℕ): Flat (flux A (evolve X) k 0 0 z):=by
    let f(i:ℕ):Vertex C:= evolve X i 0 0 z; let s (i):= X.seed i; let g(i):= f i-s i; have hf(i):Live W 0 (f i):= (lands X i 0).besides z
    have hh(i): Live W 0 (g i):= Live.sub (hf i) (X.calm i); have h(i):Flat (g i) := route_seed X
    have heq(i) : f i=s i+g i:= by unfold g; abel
    let L(a b):=traceT W 0 0 A.D a b
    let r:=∑ v∈Finset.antidiagonal k,(L (g v.1) (f v.2)+L (s v.1) (g v.2))
    rw [steady]; change Flat (command A f k)
    have eq : command A f k=command A X.seed k+(traceR W 0 A.R (g k)+(2:ℂ)⁻¹ • r):=by
       have hu(v w:ℕ):L (f v) (f w)=L (s v) (s w)+(L (g v) (f w)+L (s v) (g w)):=by
          unfold L; rw [heq v, heq w]; simp only [Static.plus_T,Static.plus_T']; abel -- caution v=w rewriting occurs dependent g?
       unfold command; change traceR W _ _ _+(2:ℂ)⁻¹ •(∑ i∈_, L (f _) (f _))=_; rw [heq k,Static.plus_R]; simp_rw [hu,Finset.sum_add_distrib]; unfold r; rw [smul_add,Finset.sum_add_distrib]; abel
    rw [eq]; refine Scale.Flat.plus (ha k) (Scale.Flat.plus (Pale.flat_row (hh k) A.hw (h k)) (Scale.Flat.scalar _ (Scale.Flat.sum (fun i hi=>?_))))
    exact Scale.Flat.plus (Pale.flat_tree (hh _) (hf _) (Or.inr (Or.inl (h _)))) (Pale.flat_tree (X.calm _) (hh _) (Or.inr (Or.inr (h _))))
end YM.MSbar.Play.Produce.Shield
