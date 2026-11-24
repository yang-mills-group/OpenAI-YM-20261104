import YM.Integration.WilsonIndependentConditionedPivotTailLaw
import YM.Integration.WilsonIndependentMatchedRosterChronology

/-! The upper first-join identity with distinct reporting dates, positions
and physical apertures for the individually normalized pivot columns. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedPivotTailHomes
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open scoped BigOperators Topology Classical
variable {G:Gauge}{n e:ℕ}{E:Credit}

abbrev rows (R:Realm G (e+1) E)(Q:Fin (n+1)→SealR G)(φ:Wilt Q)(X:Herit Q)(home:Fin (n+1)→ℕ)
    (z:Fin (n+1)→ℝ)(o:Fin (n+1)→CellR)(j N:ℕ):Fin (n+1)→Era G ℝ:=
  fun s=>locale (o s) ((Q s).spins R.draws R.paid (φ s) (home s) j N (z s) (X s))

def received (R:Realm G (e+1) E)(Q:Fin (n+1)→SealR G)(φ:Wilt Q)(X:Herit Q)(home:Fin (n+1)→ℕ)
    (z:Fin (n+1)→ℝ)(o:Fin (n+1)→CellR)(host j N:ℕ):Era G ℝ:=
  cruises R.draws R.paid N (capP Q) j host (MassP G ℝ n (rows R Q φ X home z o j N))

def first (R:Realm G (e+1) E)(Q:Fin (n+1)→SealR G)(φ:Wilt Q)(X:Herit Q)(home:Fin (n+1)→ℕ)
    (z:Fin (n+1)→ℝ)(o:Fin (n+1)→CellR)(j N:ℕ):Era G ℝ:=
  DeltaGap R.draws R.paid j N (rows R Q φ X home z o (j+1) N) (fun s=>(Q s).h)

def deposit (R:Realm G (e+1) E)(Q:Fin (n+1)→SealR G)(φ:Wilt Q)(X:Herit Q)(home:Fin (n+1)→ℕ)
    (z:Fin (n+1)→ℝ)(o:Fin (n+1)→CellR)(host j N:ℕ):Era G ℝ:=
  cruises R.draws R.paid N (capP Q) j host (first R Q φ X home z o j N)

theorem original {H:Hol G}{W V:Credit}(R:Realm G (e+1) E)(Q:Fin (n+1)→SealR G)(sold:HorizonP H R W V Q)
    (φ:Wilt Q)(X:Herit Q)(home:Fin (n+1)→ℕ)(z:Fin (n+1)→ℝ)(o:Fin (n+1)→CellR)(host K N:ℕ)
    (start:∀s,R.anchor ≤ home s)(past:host ≤ K)(cut:∀s,home s ≤ K)(ending:K ≤ N):
    received R Q φ X home z o host N N-received R Q φ X home z o host K N=
      ∑d∈Finset.range (N-K),deposit R Q φ X home z o host (K+d) N:=by
  let P:=fun s d=>rows R Q φ X home z o (host+d) N s
  let l:=fun s=>(Q s).h
  have step (j:ℕ)(kj:K ≤ j)(jn:j<N):
      received R Q φ X home z o host (j+1) N=received R Q φ X home z o host j N+
        deposit R Q φ X home z o host j N:=by
    have hj:host ≤ j:=past.trans kj
    have prev:host+(j-host)=j:=Nat.add_sub_of_le hj
    have next:host+(j-host+1)=j+1:=by omega
    have paid (s):Auth (l s) (P s (j-host+1)):=by
      dsimp only [P,rows,l]
      rw [next]
      exact locale_val _ (passportHead (sold s).some (φ s) (X s) (z s)
        ((start s).trans ((cut s).trans (kj.trans (Nat.le_succ _)))) jn) (o s)
    have moved (s):verseI R.draws R.paid (host+(j-host)) N (l s) (P s (j-host+1))=P s (j-host):=by
      dsimp only [P,rows,l];rw [prev,next]
      exact passportCarry (sold s).some (φ s) (X s) (o s) (start s) ((cut s).trans kj) jn
    have billed:=WilsonIndependentMatchedRosterChronology.edge R host (j-host) l P (by simpa only [prev] using jn) paid moved
    simpa only [received,deposit,first,capP,WilsonIndependentMatchedRosterChronology.mass,
      WilsonIndependentMatchedRosterChronology.born,P,l,prev,next] using billed
  have grow (k:ℕ)(h:K+k ≤ N):
      received R Q φ X home z o host (K+k) N=
        received R Q φ X home z o host K N+∑d∈Finset.range k,deposit R Q φ X home z o host (K+d) N:=by
    induction k with
    | zero=>simp
    | succ d ih=>
      rw [Finset.sum_range_succ]
      calc
        _=received R Q φ X home z o host (K+d) N+deposit R Q φ X home z o host (K+d) N:=
          step (K+d) (Nat.le_add_right ..) (by omega)
        _=_:=by rw [ih (by omega)];abel
  have length:K+(N-K)=N:=Nat.add_sub_of_le ending
  have full:=grow (N-K) length.le
  rw [length] at full
  rw [full]
  abel

end YM.Integration.WilsonIndependentConditionedPivotTailHomes

