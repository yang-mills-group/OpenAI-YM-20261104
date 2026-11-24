import YM.Integration.WilsonRootedHeldPacketGerm
import YM.Integration.WilsonRegisteredKineticSalary
import YM.LocalTaylorR2.Mesh.Flat
import YM.WilsonCoeffUV.Reclosure.Paths.RetainBase

/-! Joint Taylor remainder of a genuine ordered pair of incoming kinetic paths
on the physical forest. The base link field includes the held holonomy. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonHeldKineticPathTaylor
open Lattice Wilson RG Tree Pressure Precision Stationary
open ConnectedActivityE6 Coat Control Blaze Push Push.Uniform Push.AbsoluteSums
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open RG01.Sounder WilsonRootedHeldPacketGerm
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}

def pair (K : PathData G) (X : Coat T F) (s : Signed) (o : Site f) (i : PairsIndex) :
    Directions G f → ℝ := fun u => (gramPath K i).unmasked (pull s 0 (X.input u)) o

private theorem regular (K : PathData G) {B : Clip} {σ D Λ : ℝ} (paid : K.Bounds B σ D Λ)
    (X : Coat T F) (s : Signed) (o : Site f) (i : PairsIndex) (j : ℕ) (u : Directions G f) :
    Brush j ((gramPath K i).budget σ * tariff G 2 j σ) 1 (pair K X s o i) u := by
  let b : book G 2 := ⟨tides K, σ, gramCost G D, paid.width, tides_pay paid, tones K⟩
  have h := b.summand X.input u (links X j u) s o ((towers G K).symm i)
  have h' : Allows j (pair K X s o i) u ((gramPath K i).budget σ * tariff G 2 j σ) := by
    change Allows j (fun z : Directions G f => (gramPath K i).unmasked (pull s 0 (X.input z)) o)
      u ((gramPath K i).budget σ * tariff G 2 j σ)
    simpa only [b, tides, Function.comp_apply, Equiv.apply_symm_apply, book.premium, tariff] using h
  exact ⟨h'.analytic.of_le le_top, zero_le_one, fun k hk => by
    simpa only [one_pow, mul_one, normJ] using h'.norm_le k hk⟩

/-- The Taylor polynomial is taken once through degree r+2 in all link
increments of the pair. Every tested derivative acts on this same remainder. -/
theorem tested (K : PathData G) {B : Clip} {σ D Λ : ℝ} (paid : K.Bounds B σ D Λ)
    (X : Coat T F) (s : Signed) (o : Site f) (i : PairsIndex) (r k : ℕ)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E} {U : E → Directions G f}
    {β t : ℝ} (hp : 0 < β) (ht : 0 < t) (hs : t ≤ 1) (hu : Brush k t 1 U x) :
    Brush k (β * ((k.factorial * ((gramPath K i).budget σ * tariff G 2 (k+(r+2)+1) σ)) *
      (1+((1+1)*1):ℝ)^k * t^((r+2)+1))) 1
      (fun y => β • (pair K X s o i - Work.G05.blockTaylor (r+2) (pair K X s o i)) (U y)) x := by
  have h := LocalTaylorR2.Mesh.priced (d := r+2) ht hs
    (fun u _ => regular K paid X s o i (k+(r+2)+1) u) hu
  simpa only [Real.norm_of_nonneg hp.le] using h.smul β

end YM.Integration.WilsonHeldKineticPathTaylor
