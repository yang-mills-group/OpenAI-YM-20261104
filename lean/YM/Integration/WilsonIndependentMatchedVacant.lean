import YM.Integration.WilsonIndependentMatchedCoverDate
import YM.WilsonCoeffUV.Product.Report.Shapes

/-! A native missed seat contributes zero at its genuine later entrance. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedVacant
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile
open scoped BigOperators Topology Classical
variable {G:Gauge}{e:ℕ}{E:Credit}

theorem absent {D:ℕ}(P:TowerS G D)(φ:Rarity D)(x y:ℝ)(o:CellR)(l:ℕ)(hx:0<x)
    (miss:¬(VisitsT φ x y o).Nonempty): word P φ x y o l=0:=by
  rw [word,pupil_eye l P φ x y o hx,Finset.not_nonempty_iff_eq_empty.mp miss,Finset.sum_empty]

private lemma right (P:Era G ℝ):agateV P 0=0:=
  Prod.ext (funext fun _=>(woadNull _).1) (woadNull _).1
private lemma left (P:Era G ℝ):agateV 0 P=0:=
  Prod.ext (funext fun _=>(woadNull _).2) (woadNull _).2

theorem joined (R:Realm G (e+1) E)(m i N l r:ℕ)(hi:m ≤ i)(hn:i<N)
    (P Q:Era G ℝ)(miss:P=0 ∨ Q=0):
    cruises R.draws R.paid N (l+r) i m (JoinGap R.draws R.paid i N l r P Q)=0:=by
  have nil:JoinGap R.draws R.paid i N l r P Q=0:=by
    unfold JoinGap
    rcases miss with h|h
    · rw [h,left,verseZero R.draws hn R.hG R.green,verseZero R.draws hn R.hG R.green,left,sub_self]
    · rw [h,right,verseZero R.draws hn R.hG R.green,verseZero R.draws hn R.hG R.green,right,sub_self]
  rw [nil]
  induction hi using Nat.decreasingInduction with
  | self=>rw [cruises_top]
  | of_succ t ht ih=>rw [cruises_sub _ _ _ _ _ ht,ih,verseZero R.draws (ht.trans hn) R.hG R.green]

lemma zero {u:ℕ}{A:ℝ}(paid:0 ≤ A):Flush e u 1 (0:Era G ℝ) A:=
  ⟨paid,fun _ _ _ _=>Fruit.zero.more paid⟩

end YM.Integration.WilsonIndependentMatchedVacant
