import YM.Integration.WilsonIndependentMatchedFiledAtSix
import YM.Integration.WilsonIndependentMatchedCoverCrossing
import YM.WilsonCoeffUV.Product.Report.Fcut
import YM.WilsonCoeffUV.Horizon.Restore

/-! The finite projected source is carried before the first two-source join.
The exact older response includes the independent product and every earlier covariance. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedCoverCarried
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile
open scoped BigOperators Topology Classical
variable {G:Gauge}{h D k e u m N:ℕ}{F:Labels.Frame G h}
    {H:Hol G}{T:SectionData F}{p:h<D}{v:Rails h k u e}{E W K U:Credit}

theorem carried (X:CutsP H T p v E W K U)(i:ℕ)(hi:i<X.i)(a:ℝ)(φ:Rarity D)
    (x y:ℝ)(o:CellR)(hx:0<x):
    verseI X.ax X.tx (X.m+i) X.N k (word (a • X.springP (i+1)) φ x y o h)=
      word (a • X.springP i) φ (x*(X.ax.S.block (X.m+i)).val) y o h := by
  have edge:X.m+i<X.N:=lt_of_lt_of_le (Nat.add_lt_add_left hi _) (X.hc.trans X.hn)
  have authentic:=X.onward (Nat.succ_le_of_lt hi)
  have funded:=placed h φ (authentic.μ a) x y
  unfold word locale
  rw [←ply_verse X.ax edge X.vesselsC.hG X.vesselsC.green funded,
    journey φ _ X.ax X.vesselsC.hG X.vesselsC.green (authentic.μ a) y hx edge h,
    Scopes.supp edge X.vesselsC.hG X.vesselsC.green _ authentic a,X.carve2 hi]

/-- Ordinary two-source transfer on a specified earlier receiver. Both old
scalar terms and the newly formed connected field use its actual quiet. -/
theorem deposited (A:Levels G)(Ñ:ChartRatio G)(g:G.Simple)(f:LocalRatio Ñ)
    {b i l r:ℕ}(before:b ≤ i)(edge:i<N)(P Q J Z:Era G ℝ)
    (hp:Auth l P)(hq:Auth r Q)
    (stepP:verseI A Ñ i N l P=J)(stepQ:verseI A Ñ i N r Q=Z):
    cruises A Ñ N (l+r) (i+1) b (agateV P Q)=
      cruises A Ñ N (l+r) i b (agateV J Z)+
        cruises A Ñ N (l+r) i b (JoinGap A Ñ i N l r P Q) := by
  subst J
  subst Z
  have left:=Auth.verse A edge g f (hp.manor hq)
  have right:=(Auth.verse A edge g f hp).manor (Auth.verse A edge g f hq)
  unfold JoinGap
  rw [cruisePlus A before g f edge.le left right,cruiseStep A Ñ _ before]
  abel

/-- Each deposited join is propagated only once through the remaining
normalized chronology. The equality holds in the entire field space. -/
theorem original (R:Realm G (e+1) E)(l r m N n:ℕ)(span:m+n≤N)
    (P Q:ℕ→Era G ℝ)(hp:∀i≤n,Auth l (P i))(hq:∀i≤n,Auth r (Q i))
    (left:∀i<n,verseI R.draws R.paid (m+i) N l (P (i+1))=P i)
    (right:∀i<n,verseI R.draws R.paid (m+i) N r (Q (i+1))=Q i):
    cruises R.draws R.paid N (l+r) (m+n) m (agateV (P n) (Q n))=
      agateV (P 0) (Q 0)+∑i∈Finset.range n,cruises R.draws R.paid N (l+r) (m+i) m
        (JoinGap R.draws R.paid (m+i) N l r (P (i+1)) (Q (i+1))) := by
  induction n with
  | zero => simp [cruises_top]
  | succ n ih =>
    have previous:=ih (by omega) (fun i hi=>hp i (by omega)) (fun i hi=>hq i (by omega))
      (fun i hi=>left i (by omega)) (fun i hi=>right i (by omega))
    rw [Finset.sum_range_succ,←add_assoc (agateV (P 0) (Q 0)) _ _,←previous]
    exact deposited R.draws R.paid R.hG R.green (Nat.le_add_right m n) (by omega) _ _ _ _
      (hp _ le_rfl) (hq _ le_rfl) (left n (Nat.lt_succ_self _)) (right n (Nat.lt_succ_self _))

end YM.Integration.WilsonIndependentMatchedCoverCarried
