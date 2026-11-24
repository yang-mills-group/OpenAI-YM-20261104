import YM.Integration.WilsonSeparatedPrefixMovingFirstTree
import YM.Integration.WilsonSeparatedPrefixMovingPairSector

/-! The exact mixed face at a fixed older receiver. Old deposits remain in
the conditional product through every subsequent edge. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingSignedChronology
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonSeparatedPrefixMovingPairSector (current)
open Finset
open scoped BigOperators Topology Classical

variable {G:Gauge}{e:ℕ}{E:Credit}

theorem added (R:Realm G (e+1) E)(k top bottom N:ℕ)(le:bottom ≤ top)(paid:top ≤ N)
    (P Q:Era G ℝ)(p:Auth k P)(q:Auth k Q):
    cruises R.draws R.paid N k top bottom (P+Q)=cruises R.draws R.paid N k top bottom P+
      cruises R.draws R.paid N k top bottom Q:=by
  have h:=cruisePlus R.draws le R.hG R.green paid (p.add q) q
  rw [add_sub_cancel_right] at h
  exact eq_add_of_sub_eq h.symm

theorem read (R:Realm G (e+1) E)(k top bottom N n:ℕ)(le:bottom ≤ top)(paid:top ≤ N)
    (P:Era G ℝ)(D:ℕ→Era G ℝ)(p:Auth k P)(d:∀i<n,Auth k (D i)):
    cruises R.draws R.paid N k top bottom (P+∑i∈range n,D i)=
      cruises R.draws R.paid N k top bottom P+∑i∈range n,cruises R.draws R.paid N k top bottom (D i):=by
  have sworn (m:ℕ)(bound:m ≤ n):Auth k (P+∑i∈range m,D i):=by
    induction m with
    | zero=>simpa using p
    | succ m ih=>rw [sum_range_succ,←add_assoc];exact (ih (by omega)).add (d _ (by omega))
  induction n with
  | zero=>simp
  | succ n ih=>
    have sub:∀i<n,Auth k (D i):=fun i h=>d _ (by omega)
    rw [sum_range_succ,sum_range_succ,←add_assoc,added R k top bottom N le paid
      (P+∑i∈range n,D i) (D n) (sworn n (Nat.le_succ _)) (d n (by omega)),
      ih sub (fun m hm=>sworn m (by omega)),add_assoc]

theorem split (R:Realm G (e+1) E)(l r older m N n:ℕ)(home:older ≤ m)(span:m+n ≤ N)
    (P Q:ℕ→Era G ℝ)(hp:∀i ≤ n,Auth l (P i))(hq:∀i ≤ n,Auth r (Q i))
    (left:∀i<n,verseI R.draws R.paid (m+i) N l (P (i+1))=P i)
    (right:∀i<n,verseI R.draws R.paid (m+i) N r (Q (i+1))=Q i):
    cruises R.draws R.paid N (l+r) (m+n) older (agateV (P n) (Q n))=
      cruises R.draws R.paid N (l+r) m older (agateV (P 0) (Q 0))+
        ∑i∈range n,cruises R.draws R.paid N (l+r) (m+i) older
          (JoinGap R.draws R.paid (m+i) N l r (P (i+1)) (Q (i+1))):=by
  induction n with
  | zero=>simp
  | succ n ih=>
    have previous:=ih (by omega) (fun i hi=>hp i (by omega)) (fun i hi=>hq i (by omega))
      (fun i hi=>left i (by omega)) (fun i hi=>right i (by omega))
    rw [sum_range_succ,←add_assoc (cruises R.draws R.paid N (l+r) m older (agateV (P 0) (Q 0))),←previous]
    exact WilsonIndependentMatchedCoverCarried.deposited R.draws R.paid R.hG R.green
      (show older ≤ m+n by omega) (by omega) _ _ _ _ (hp _ le_rfl) (hq _ le_rfl)
      (left n (Nat.lt_succ_self _)) (right n (Nat.lt_succ_self _))

theorem simple(R:Realm G (e+1) E)(d v w i N:ℕ)(actual:i<N)
    (E₀ A B:Era G ℝ)(he:Auth d E₀)(ha:Auth v A)(hb:Auth w B):
    Auth (d+(v+w)) (JoinGap R.draws R.paid i N d (v+w) E₀ (agateV A B)):=
  (Auth.verse R.draws actual R.hG R.green (he.manor (ha.manor hb))).sub
    ((Auth.verse R.draws actual R.hG R.green he).manor (Auth.verse R.draws actual R.hG R.green (ha.manor hb)))

end YM.Integration.WilsonSeparatedPrefixMovingSignedChronology
