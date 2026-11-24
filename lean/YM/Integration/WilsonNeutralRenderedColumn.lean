import YM.Integration.WilsonOlderFreshGraphArmada
import YM.Integration.FVA1Physical.TwoReset.CopyLetters

/-! The actual nonbare normalized one-mark teacher inside the finite forest
reader. Each input component is the purchased curvature word on its own
translated physical links, with its exact pole-clearing power. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonNeutralRenderedColumn
open Finset Function Lattice Wilson RG Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise
open Comparison.RG02.Bulk Next.SectorChange Multi AllOrder AllOrder.Floe
open Further.PhysicalPeriodLimitF933 Macrame Shingle QuadraticLocal.Poetry
open FVA1Physical.TwoReset WilsonOlderFreshGraphVote WilsonOlderFreshGraphMount
open scoped BigOperators Classical
variable {G:Gauge} {n n':Side} {Q d:ℕ} {α:Type}
variable {P:Earn.Passport n Unit} {H:Marker.Census Unit} (S:Earn.Binder P H)
variable (W:Fin (Q+1)→Poetry.Roll G Unit) (C:Fin (Q+1)→ℝ) (σ:ℝ)
variable (paid:∀j,(W j).Faith {()} () (j.val+d+2) (2*σ) (C j))
variable (legal:∀j,(W j).honest) (d0:0<d) (weight:α→ℂ)
local notation "M" => material S W C σ paid legal d0 weight
def submitted : Multi.Hot H := ⟨S.mode,(Comparison.RG02.Cumulants.hot_iff_ne S.mode).2 S.live⟩

def word (j:Name W) (s:ℝ) (x:α) (o:Site n') (U:Config G n') : ℂ :=
  let Y:=(W j.1).leg j.2.1
  weight x * (s^(j.1.val+d+1-Y.r)*Y.atom.unmasked U o:ℝ)

theorem painted (j:Name W) (s:ℝ) (x:α) (o:Site n') (U:Config G n') :
    (M j).paint x * (Loan.letter (M j).lamp (M j).atom o s U:ℝ) =
      word (d:=d) W weight j s x o U := by
  let Y:=(W j.1).leg j.2.1
  change ((fare Y σ:ℝ):ℂ)*weight x *
    (↑(s^(j.1.val+d+1-Y.r)*(Bloom.letdown Y.atom (fare Y σ)⁻¹).unmasked U o):ℂ)=_
  unfold word
  rw [Bloom.grant]
  push_cast
  have nz:(fare Y σ:ℂ)≠0:=Complex.ofReal_ne_zero.mpr
    (mul_pos j.2.2 (Real.exp_pos _)).ne'
  change _=weight x*((s:ℂ)^(j.1.val+d+1-Y.r)*↑(Y.atom.unmasked U o))
  field_simp [nz]

theorem original (x:α) (layout:Layout G) (stock:Finset Age) (s:ℝ) (U:Config G n) :
    (Air.craft M (fun i=>(M i).paint x) (fun _=>d) layout stock).mark (submitted S) s U =
      ∑' j:Name W, word (d:=d) W weight j s x S.center U := by
  classical
  unfold Air.craft QuadraticLocal.Fk.grant Air.sums
  apply tsum_congr
  intro j
  rw [if_pos (show (ScatterR.actor M j).val=(submitted S).val from rfl)]
  exact painted S W C σ paid legal d0 weight j s x S.center U

theorem copied (h:n.val∣n'.val) (x:α) (layout:Layout G) (stock:Finset Age) (s:ℝ) (U:Config G n') :
    (copyColor h M (fun _=>d) (fun j=>(M j).paint x) layout stock).mark (submitted S) s U =
      ∑ p:Fin (Pages n n'), ∑' j:Name W, word (d:=d) W weight j s x
        (FVA1Physical.TwoReset.copy h (M j) p).center U := by
  classical
  unfold copyColor
  simp only [Finset.sum_apply]
  refine Finset.sum_congr rfl fun p _=>?_
  simp only [Air.craft,QuadraticLocal.Fk.grant,Air.sums]
  apply tsum_congr
  intro j
  rw [if_pos (show (ScatterR.actor (fun z=>FVA1Physical.TwoReset.copy h (M z) p) j).val=(submitted S).val from rfl)]
  exact painted S W C σ paid legal d0 weight j s x _ U

end YM.Integration.WilsonNeutralRenderedColumn
end
