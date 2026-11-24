import YM.Integration.WilsonOlderFreshConnectedCurrency
import YM.Integration.WilsonOlderFreshConnectedBoard
import YM.Integration.OriginalRunMarkedPacketPurchase
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshConnectedEarning
open Function Filter Finset MeasureTheory Lattice RG Precision Wilson Tree Exterior
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.Express WilsonCoeffUV.Embroider
open WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Soil WilsonCoeffUV.Wheel.Flooring
open Work.F08
open scoped BigOperators Classical


open FundedMarkedPathSelection
open PhysicalNext.Repeat.Legato WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Embroider.Canvas
open ComparisonDensity.Address WilsonCoeffUV.Shard WilsonCoeffUV.Winding OriginalIssuedMarkedRows
open ActualRunAdmissionScales OriginalBareMarkedInvoice Filter Function
open WilsonOlderFreshConnectedRobe WilsonCoeffUV.Bank.Ticket
open scoped Topology
variable {G:Gauge}{n e m N l b t:ℕ}{A:ℝ}{k D:Fin n  →  ℕ}{S J:Finset (Fin n)}{c:Fin n}


open WilsonOlderFreshConnectedBoard Push.PriceCompiler
variable {I:Type}

private theorem lease_le {r:ℕ}{J:Finset I}{D:I → ℕ}(P:Comet G (Pen D J) r)
    (μ:Stationary.Ink G r → Measure (Sky D)){a b:ℝ}(h:a ≤ b):lease P μ a ≤ lease P μ b:=by
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
  unfold Atom.budget
  apply mul_le_mul_of_nonneg_left _ (by unfold Atom.magnitude; positivity)
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right h (Nat.cast_nonneg _))

theorem payroll (Q:Realm G (e+1) Credit.leanC)(hm:Q.anchor ≤ m)(X:Input Q hm S k D A)
    {w w' u:ℝ}{o:Cover}{j:ℕ}{r:Fin (l+j+1)}(p:Rooted Q hm X J c l N w u o j r)(h:w' ≤ w):
    Rooted Q hm X J c l N w' u o j r:=by
  obtain ⟨μ,born,heard,raw,dress⟩:=p
  let pkg:=fun x:Frill J c × RadP G r.val=>packetH J (output X J N) l (e+1) c o x.1 j r x.2
  let fee:=fun (s:ℝ)(x:Frill J c × RadP G r.val)=>Real.exp (s*feeH (toe J c o x.1) c J)*lease (pkg x) (μ x) s
  have nn(s)(x):0 ≤ fee s x:=mul_nonneg (Real.exp_pos _).le (stripV_n ..)
  have down(x):fee w' x ≤ fee w x:=by
    apply mul_le_mul _ (lease_le (pkg x) (μ x) h) (stripV_n ..) (Real.exp_pos _).le
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right h (Nat.cast_nonneg _))
  refine ⟨μ,born,heard,Work.F08.budget_minor raw (nn _) down,?_⟩
  intro g hg h1
  exact Work.F08.budget_minor (dress g hg h1)
    (fun x=>mul_nonneg (zpow_pos hg _).le (nn _ x))
    (fun x=>mul_le_mul_of_nonneg_left (down x) (zpow_pos hg _).le)

end YM.Integration.WilsonOlderFreshConnectedEarning
end
