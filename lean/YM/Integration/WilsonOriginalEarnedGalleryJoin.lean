import YM.QuadraticLocal.Lamps
import YM.Next.RANK.Exponential

/-! Joining a funded cluster input at the same compact group field retains
the entire earlier hard packet and multiplies by the new accepted entry. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalEarnedGalleryJoin
open Finset Lattice Wilson RG Marker Ac QuadraticLocal
open scoped BigOperators Classical
variable {G : Gauge} {n : Side} {V α I J : Type} [DecidableEq V] [Fintype V]
  {P : RG.Rep G n} {Γ : Census V} {o : V → Site n}

def joined (b:Gallery α J o P Γ) (f:Lamps α I G P.p o Γ) : Gallery α (I ⊕ J) o P Γ :=
  ⟨f.join b.E,b.K⟩

theorem field (b:Gallery α J o P Γ) (f:Lamps α I G P.p o Γ)
    {w : V → ℝ} {C t : ℝ} {d : ℕ} (paid:b.E.Paid w d t C)
    (positive:0≤t) (prices:∀v,0<w v) [Fintype I] (x:α) (U:Config G n) :
    (joined b f).density x U = b.density x U * Poly.pass (f.log x U) := by
  have old := paid.sums positive prices x U
  have fresh : Summable (fun i:I => f.frame i x U) := (hasSum_fintype _).summable
  let A := Poly.pass (f.log x U)
  let B := Poly.pass (b.E.log x U)
  let z := Complex.ofReal (Real.exp (P.exponent U))
  have hpass : Poly.pass ((f.join b.E).log x U)=A*B :=
    (congrArg Poly.pass (Lamps.joinLog x U fresh old)).trans
      (Next.Rank.Exponential.pass_add _ _ (f.quiet_of_hasSum x U fresh) (b.E.quiet_of_hasSum x U old))
  calc
    _ = z • (Poly.pass ((f.join b.E).log x U) * b.gas x U) := rfl
    _ = z • ((A*B)*b.gas x U) := congrArg (fun y : Poly Γ => z • (y*b.gas x U)) hpass
    _ = z • ((B*b.gas x U)*A) :=
      congrArg (fun y : Poly Γ => z • y) ((mul_assoc A B (b.gas x U)).trans (mul_comm A (B*b.gas x U)))
    _ = _ := (smul_mul_assoc z (B*b.gas x U) A).symm

end YM.Integration.WilsonOriginalEarnedGalleryJoin
