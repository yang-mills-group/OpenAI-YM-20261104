import YM.AllOrder.Ink.Spectrum
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Ink
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace.SigmaP Ker
open Progress.ClassicalKin Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response
open scoped BigOperators Topology Classical ContDiff
variable {n m:Side} {α β : Type} [Fintype α] [Fintype β] {k N M:ℕ} {a C D b:ℝ}
namespace Money
variable {V:Type} {Λ:V→ℝ} {Ad:Side→Prop} {U : ℕ→ℕ→V→ Bills α}
open Method
variable {T: V→ℝ}{A: V→Stalk α α}
structure Code (Ad:Side→Prop) (A:V→Stalk α α)(R:ℕ→ℕ→ V→Bills α) :Prop where
  one (k v n) : Ad n→R k 1 v n=0
  pact (k r v n): Ad n→ R k (r+2) v n= (↑(r+2:ℕ):ℝ)⁻¹ • ((∑ i∈range (k+1),∑ j∈range (r+1), spark (A v) (R (k-i) (r-j) v n) (R i j v n)) + flicker (A v) n (R k r v n))
variable (HA:Grade Λ T)(H:∀ v,Belt (A v) a (T v))(h0:0<a)
variable (h:Code Ad A U)(hh:∀ k≤N,Apt Ad Λ (U k 0) (k+2))
include H HA h0 h hh
lemma launches (r k:ℕ)(hk:k≤N) : Apt Ad Λ (U k r) (k+2) := by
 induction r using Nat.strong_induction_on generalizing k with
 | h r hr=>
    rcases r with _|r; exact hh k hk
    rcases r with _|r; exact Apt.adapt (Apt.null _) (fun v n he=> (h.one k v n he).symm)
    let p(i j:ℕ) := fun (v:V) (n:Side)=> spark (A v) (U (k-i) (r-j) v n) (U i j v n); have hx(i:ℕ)(he:i≤k)(j:ℕ)(hp:j≤r): Apt Ad Λ (p i j) (k+2):= Apt.grow (Apt.join HA h0 H (hr (r-j) (by omega) (k-i) (by omega)) (hr j (by omega) i (by omega))) (by omega)
    let v:= r+1+1; let f₁:V→Bills α:=fun v n=> ∑ i ∈ range (k+1),∑ j∈range (r+1), p i j v n
    let f₂:V→Bills α:= fun v n=> flicker (A v) n (U k r v n)
    let he:= h.pact k r; exact Apt.adapt ((show Apt Ad Λ ((fun v n=> (↑(r+2:ℕ):ℝ)⁻¹ • (f₁ v n+f₂ v n)): V→Bills α) (k+2) from Apt.scale (Apt.add (Apt.pile (F:=fun i v n=>∑ j∈range (r+1),p i j v n) (range (k+1)) (fun i hi=> Apt.pile (range (r+1)) (p i) (fun j hj=> hx i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))))) ((Apt.furnish A HA h0 H (hr r (by omega) k hk)).grow (by omega))) _)) (fun v n hu=> (he v n hu).symm)
def snapshot (U:ℕ→ℕ→V→Bills α) (k:ℕ):V→Bills α:= fun v n=>∑ j∈ range (3*k+1),U k j v n
lemma settles (hk:k≤N): Apt Ad Λ (snapshot U k) (k+2) := Apt.pile _ (U k) (fun r _=>launches HA H h0 h hh r k hk)
end Money
end YM.AllOrder.Ink
