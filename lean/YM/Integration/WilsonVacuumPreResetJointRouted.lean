import YM.Integration.WilsonVacuumPreResetJointSlate
import YM.Integration.WilsonVacuumPreResetJointSeating
import YM.Integration.WilsonVacuumPreResetPrunedBirthFive

/-! The full old-spring Taylor invoice on a genuinely selected physical
receipt, with the exact Haar cell and the selected coarse/fine chart. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetJointRouted
open WilsonCoeffUV
open Function Filter Finset Lattice RG Wilson Tree Pressure Pressure.Stores Pressure.Tube
open ConnectedActivityE6 Shell Coat SliceRows Control Window Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Shoot Precision SectorMeasure Oriented Reserves
open PhysicalNext PhysicalNext.Repeat Height Beam Brim
open ConnectedActivityE6.Blaze Blaze.March Captain Silica
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonVacuumPreResetJointField WilsonVacuumPreResetJointSlate
open WilsonLimitConstruction RG01Estimate
open scoped Topology BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f}

def Sold (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (T:Tube G S)(Q:Rep G f)
    (A:SeriesA G)(s C σ D γ η ρ u:ℝ)(size:ℕ):Prop:=
  ∀(F:Forest S.ratio)(X:Coat T F)(p:Molecule S),p.toLeft=∅→flags (Pressure.temp X.x) X.V=∅→
    ∀(Y:F.Slice G)(r j:ℕ)(y:E)(z:E→Arguments G c f)(t:ℝ),0<t→t≤1→Brush j t 1 z y→
    let Z:=(Matter.planted X p).wrapY Y
    Brush j ((size:ℝ)* |tariff Q.clip A s C σ D γ η ρ u j r t|) 1
      (fun w=>physical Q.clip Q.path A γ η ρ u (field univ Z (z w))-
        published Q.clip Q.path A γ η ρ u (r+2) Z (z w)) y

variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] {T:Tube G S}{Q:Rep G f}
variable {A:SeriesA G}{s C σ D γ η ρ u Λ:ℝ}{size:ℕ}

theorem measured (h:Q.path.Bounds Q.clip s C Λ)(hs:0<σ)(draw:Draw A σ D)
    (bill:Fintype.card (Site f) ≤ size):Sold E T Q A s C σ D γ η ρ u size:=by
  intro F X p kept sun Y r j y z t ht ht' read
  have paid:=WilsonVacuumPreResetJointSlate.original h hs A draw X p kept sun Y γ η ρ u r j ht ht' read
  exact paid.climb
    ((mul_le_mul_of_nonneg_left (le_abs_self _) (Nat.cast_nonneg _)).trans
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr bill) (abs_nonneg _))) le_rfl

variable {L : Side} {P : Teller G} {B : ConnectedActivityE6.Target G P}
variable {W : ℝ} {o : Target.Order G W}
variable {w μ α : ℝ} {H : Cash W w μ L B o α T Q} {F:Forest S.ratio}

theorem seated (paid:Sold E T Q A s C σ D γ η ρ u size)(X:Coat T F)
    {off:Set ℕ}{b:H.fragrances}{d:ℕ}(chosen:Fate.showcase off d b)(i:Option (Fin b.1))(k:S.Choices)
    (sun:flags (Pressure.temp X.x) X.V=∅)(Y:F.Slice G)(r j:ℕ)(y:E)(z:E→Arguments G c f)
    (t:ℝ)(ht:0<t)(ht':t≤1)(read:Brush j t 1 z y):
    let Z:=((Matter.preps X (Matter.roster (b.2 i).val)).taggedL k).wrapY Y
    Brush j ((size:ℝ)* |tariff Q.clip A s C σ D γ η ρ u j r t|) 1
      (fun w=>physical Q.clip Q.path A γ η ρ u (field univ Z (z w))-
        published Q.clip Q.path A γ η ρ u (r+2) Z (z w)) y:=by
  let p:=(b.2 i).val
  have he:=WilsonVacuumPreResetJointBranch.no_seeds chosen i
  have eq:=WilsonVacuumPreResetJointSeating.seated (X.taggedL k) p he sun
  have sale:=paid F (X.taggedL k) p he sun Y r j y z t ht ht' read
  rw [eq] at sale
  exact sale

end YM.Integration.WilsonVacuumPreResetJointRouted
