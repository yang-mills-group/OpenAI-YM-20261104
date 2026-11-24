import YM.Integration.WilsonIndependentMovingRosterBirthCalendar

/-! On one inherited vacuum the product of the genuine K-graphs is the
unjoined upper return. Its entire difference is accounted for by first joins
on the edges from K through the microscopic cutoff, on the very same host. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedPivotTailLaw
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open scoped BigOperators Topology Classical
variable {G:Gauge}{n e:ℕ}{E:Credit}

def upper (Q:Fin (n+1)→SealR G)(R:Realm G (e+1) E)(φ:Wilt Q)(X:Herit Q)
    (host m j N:ℕ)(y:ℝ)(o:CellR):Era G ℝ:=
  cruises R.draws R.paid N (capP Q) j host (Ashore Q R.draws R.paid φ X m j N y o)

def deposit (Q:Fin (n+1)→SealR G)(R:Realm G (e+1) E)(φ:Wilt Q)(X:Herit Q)
    (host m j N:ℕ)(y:ℝ)(o:CellR):Era G ℝ:=
  cruises R.draws R.paid N (capP Q) j host (Ash R.draws R.paid φ X m j N y o)

theorem edge {H:Hol G}{W V:Credit}(Q:Fin (n+1)→SealR G)(R:Realm G (e+1) E)(issued:HorizonP H R W V Q)
    (φ:Wilt Q)(X:Herit Q){host m j N:ℕ}(start:R.anchor ≤ m)(hearing:host ≤ m)(date:m ≤ j)(live:j<N)
    (y:ℝ)(o:CellR):
    upper Q R φ X host m (j+1) N y o = upper Q R φ X host m j N y o+deposit Q R φ X host m j N y o:=by
  have coarse:=ash_head issued φ X (y:=y) (m:=m) (start.trans date) live.le o
  have child:=ash_head issued φ X (i:=j+1) (y:=y) (m:=m) (start.trans (date.trans (Nat.le_succ j))) live o
  have split:=cruisePlus R.draws (hearing.trans date) R.hG R.green live.le (Auth.verse R.draws live R.hG R.green child) coarse
  unfold upper deposit
  rw [ash_tide issued φ X start date live o,split,cruiseStep R.draws R.paid _ (hearing.trans date)]
  abel

theorem original {H:Hol G}{W V:Credit}(Q:Fin (n+1)→SealR G)(R:Realm G (e+1) E)(issued:HorizonP H R W V Q)
    (φ:Wilt Q)(X:Herit Q){host m K N:ℕ}(start:R.anchor ≤ m)(hearing:host ≤ m)(inside:m ≤ K)(last:K ≤ N)
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
          edge Q R issued φ X start hearing (inside.trans (Nat.le_add_right K d)) (by omega) y o
        _=_:=by rw [done (by omega)];abel
  have length:K+(N-K)=N:=Nat.add_sub_of_le last
  have accrued:=work (N-K) length.le
  rw [length] at accrued
  rw [accrued]
  abel

end YM.Integration.WilsonIndependentConditionedPivotTailLaw

