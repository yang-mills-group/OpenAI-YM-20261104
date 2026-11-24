import YM.FullVolume.Mark.Hinge
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Matric
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}{B:SectionData F}{H:History G} {N p m:ℕ} {Y:Hol G}
variable {S: Desk G (H.S.side (m+1) p)}{E:Desk G (H.S.side m p)}
set_option quotPrecheck false
local notation "T₀" => H.rep N p m
local notation "T₁" => H.rep N p (m+1)
local notation "U₀"=> (H.levels.params m).columns
local notation "U₁"=> (H.levels.params (m+1)).columns
local notation "k₀"=> kappa H m
local notation "k₁"=> Real.sqrt (H.levels.clock.forcedAllowance (m+1))
set_option quotPrecheck false
variable (P : Tool F H N p m){W:Worth}{u ζ v t:ℝ}{D:GaugeDoor (H.rep N p (m+1)) (H.rep N p m)}{T:Heading F}{X:Set Wing}
variable (h:Tool.Cap P B Y W D T u ζ v X) (hw:Well (H.rep N p (m+1)) S (Real.sqrt (H.levels.clock.forcedAllowance (m+1)))) (hu:Well (H.rep N p m) E (Real.sqrt (H.levels.clock.forcedAllowance m))) (hp: roomCost H.levels W)(hk:Bank W H.levels)
namespace Gram
variable (Q:Gram F Y S ((H.levels.params (m+1)).columns))
include h hw
theorem signedPoint (v : F.Coeff) :
    F.coeffSize ((Q.point P v).x-T.leads (H.S.block m) v) ≤ barunit (H.S.block m)*F.coeffSize (F.core v) := by
  let f (i:F.Index) := (P.shot i (Coin.uses (Q.scythe i))).x
  have he (i:Tally F) := P.scout h hw Q.scythe (fun i=>Q.toll _) i
  have hZ : (Q.point P v).x = repaint F f v := by
    unfold point Tool.pages
    rw [pencil_x]
    exact Finset.sum_congr rfl fun i _=>congr_arg (chips F v i • ·) (Tool.portX P h hw Q.scythe i)
  rw [hZ]
  have hs : 0 ≤ (H.levels.params (m+1)).columns := zero_le_one.trans (H.levels.params (m+1)).columns_ge
  exact (budgets_orbit F (H.S.block m) T f v (ζ*(1+(H.levels.params (m+1)).columns))
    (mul_nonneg h.budget.epsilon (by positivity)) (fun i=> (he i).2.1)).trans
    (mul_le_mul_of_nonneg_right h.budget.tiny (Work.G08.size_nonneg F _))

end Gram
end YM.MergeProof.Matric
