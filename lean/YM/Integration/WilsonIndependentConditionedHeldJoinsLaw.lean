import YM.Integration.WilsonIndependentConditionedPivotTailLaw

/-! On one inherited vacuum the product of the genuine K-graphs is the
unjoined upper return. Its entire difference is accounted for by first joins
on the edges from K through the microscopic cutoff, on the very same host. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedHeldJoinsLaw
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open scoped BigOperators Topology Classical
variable {G:Gauge}{n e:ℕ}{E:Credit}

open WilsonIndependentConditionedPivotTailLaw (upper deposit)
theorem edge {H:Hol G}{W V:Credit}(Q:Fin (n+1)→SealR G)(R:Realm G (e+1) E)(issued:HorizonP H R W V Q)
    (φ:Wilt Q)(X:Herit Q){host m j N:ℕ}(start:R.anchor ≤ m)(hearing:host ≤ j)(date:m ≤ j)(live:j<N)
    (y:ℝ)(o:CellR):
    upper Q R φ X host m (j+1) N y o = upper Q R φ X host m j N y o+deposit Q R φ X host m j N y o:=by
  have coarse:=ash_head issued φ X (y:=y) (m:=m) (start.trans date) live.le o
  have child:=ash_head issued φ X (i:=j+1) (y:=y) (m:=m) (start.trans (date.trans (Nat.le_succ j))) live o
  have split:=cruisePlus R.draws hearing R.hG R.green live.le (Auth.verse R.draws live R.hG R.green child) coarse
  unfold WilsonIndependentConditionedPivotTailLaw.upper deposit
  rw [ash_tide issued φ X start date live o,split,cruiseStep R.draws R.paid _ hearing]
  abel

theorem original {H:Hol G}{W V:Credit}(Q:Fin (n+1)→SealR G)(R:Realm G (e+1) E)(issued:HorizonP H R W V Q)
    (φ:Wilt Q)(X:Herit Q){host m K N:ℕ}(start:R.anchor ≤ m)(hearing:host ≤ K)(inside:m ≤ K)(last:K ≤ N)
    (y:ℝ)(o:CellR):
    upper Q R φ X host m N N y o - upper Q R φ X host m K N y o =
      ∑d∈Finset.range (N-K),deposit Q R φ X host m (K+d) N y o:=by
  have work (d:ℕ)(top:K+d ≤ N):
      upper Q R φ X host m (K+d) N y o=upper Q R φ X host m K N y o+
        ∑i∈Finset.range d,deposit Q R φ X host m (K+i) N y o:=by
    induction d with
    | zero=>simp
    | succ d done=>
      rw [Finset.sum_range_succ]
      calc
        _=upper Q R φ X host m (K+d) N y o+deposit Q R φ X host m (K+d) N y o:=
          edge Q R issued φ X start (hearing.trans (Nat.le_add_right K d)) (inside.trans (Nat.le_add_right K d)) (by omega) y o
        _=_:=by rw [done (by omega)];abel
  have length:K+(N-K)=N:=Nat.add_sub_of_le last
  have accrued:=work (N-K) length.le
  rw [length] at accrued
  rw [accrued]
  abel

/-- All earlier joins at the authentic fine reporter, at the actual cell rather than an averaged scalar. -/
theorem held {H:Hol G}{W V:Credit}(Q:Fin (n+1)→SealR G)(R:Realm G (e+1) E)
    (issued:HorizonP H R W V Q)(φ:Wilt Q)(X:Herit Q){m K N:ℕ}(start:R.anchor ≤ m)(inside:m ≤ K)(last:K ≤ N)
    (y:ℝ)(o:CellR):
    locale o (LodeStar R.draws R.paid φ X m K N y)-Ashore Q R.draws R.paid φ X m K N y o=
      ∑d∈Finset.range (N-K),deposit Q R φ X K m (K+d) N y o:=by
  have full:locale o (LodeStar R.draws R.paid φ X m K N y)=upper Q R φ X K m N N y o:=by
    unfold WilsonIndependentConditionedPivotTailLaw.upper LodeStar locale
    rw [cruiseT (century o) _ last R.hG R.green le_rfl
      (Hearth_enter issued φ X (start.trans (inside.trans last)) le_rfl),ash_spans]
  have row:=original Q R issued φ X start (host:=K) le_rfl inside last y o
  rw [full]
  simpa only [WilsonIndependentConditionedPivotTailLaw.upper,cruises_top] using row

end YM.Integration.WilsonIndependentConditionedHeldJoinsLaw
