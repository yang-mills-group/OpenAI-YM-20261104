import YM.Integration.WilsonSeparatedPrefixMovingSignedChronology
import YM.Integration.WilsonSeparatedPrefixMovingPinWallet

/-! The same lattice pin on every new connected deposit, heard on the actual older law. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingPinHearing
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonSeparatedPrefixMovingPairSector (current)
open Finset
open scoped BigOperators Topology Classical

open WilsonPositionProgramPinnedHearthHistory (pin)
variable {G:Gauge}{e:ℕ}{E:Credit}

def shiftHom (a:Cover):Era G ℝ →+ Era G ℝ where
  toFun:=fun X=>shifted X a
  map_zero':=rfl
  map_add':=fun _ _=>rfl

def hear (R:Realm G (e+1) E)(k N b older:ℕ)(a:Cover)(i:ℕ)(X:Era G ℝ):Era G ℝ:=
  cruises R.draws R.paid N k i older (shiftHom (pin R.draws.S b i a) X)

theorem tower (R:Realm G (e+1) E)(k N b older j i:ℕ)(a:Cover)(X:Era G ℝ)(Hx:Auth k X)
    (old:older ≤ j)(gate:b ≤ j)(edge:j ≤ i)(full:i ≤ N):
    hear R k N b older a j (cruises R.draws R.paid N k i j X)=hear R k N b older a i X:=by
  unfold hear
  change cruises _ _ _ _ _ _ (shifted (cruises _ _ _ _ _ _ X) _)=_
  rw [←WilsonPositionProgramPinnedHearthHistory.at_date R.draws R.hG R.green X Hx a full edge gate]
  exact (cruisesMore R.draws R.paid _ old edge).symm

theorem register (R:Realm G (e+1) E)(k N b older i n:ℕ)(a:Cover)(P:Era G ℝ)
    (D:ℕ→Era G ℝ)(old:older ≤ i)(full:i ≤ N)(hp:Auth k P)(hd:∀j<n,Auth k (D j)):
    hear R k N b older a i (P+∑j∈range n,D j)=
      hear R k N b older a i P+∑j∈range n,hear R k N b older a i (D j):=by
  simp only [hear,map_add,map_sum]
  exact WilsonSeparatedPrefixMovingSignedChronology.read R k i older N n old full _ _ (hp.shifted _)
    (fun j hj=>(hd j hj).shifted _)

theorem subtract (R:Realm G (e+1) E)(k N b older i:ℕ)(a:Cover)(P Q:Era G ℝ)
    (old:older ≤ i)(full:i ≤ N)(hp:Auth k P)(hq:Auth k Q):
    hear R k N b older a i (P-Q)=hear R k N b older a i P-hear R k N b older a i Q:=by
  simp only [hear,map_sub]
  exact cruisePlus R.draws old R.hG R.green full (hp.shifted _) (hq.shifted _)

theorem split (R:Realm G (e+1) E)(l r b older m N n:ℕ)(a:Cover)(home:older ≤ b)(gate:b ≤ m)
    (span:m+n ≤ N)(P Q:ℕ→Era G ℝ)(hp:∀i ≤ n,Auth l (P i))(hq:∀i ≤ n,Auth r (Q i))
    (left:∀i<n,verseI R.draws R.paid (m+i) N l (P (i+1))=P i)
    (right:∀i<n,verseI R.draws R.paid (m+i) N r (Q (i+1))=Q i):
    hear R (l+r) N b older a (m+n) (agateV (P n) (Q n))=
      hear R (l+r) N b older a m (agateV (P 0) (Q 0))+
        ∑i∈range n,hear R (l+r) N b older a (m+i)
          (JoinGap R.draws R.paid (m+i) N l r (P (i+1)) (Q (i+1))):=by
  let k:=l+r
  let birth i:=JoinGap R.draws R.paid (m+i) N l r (P (i+1)) (Q (i+1))
  have valid (i:ℕ)(hi:i<n):Auth k (birth i):=by
    have h:m+i<N:=by omega
    have L:=hp (i+1) (by omega)
    have U:=hq (i+1) (by omega)
    exact (Auth.verse R.draws h R.hG R.green (L.manor U)).sub
      ((Auth.verse R.draws h R.hG R.green L).manor (Auth.verse R.draws h R.hG R.green U))
  have due:=WilsonSeparatedPrefixMovingSignedChronology.split R l r b m N n gate span P Q hp hq left right
  have pulled:=congrArg (hear R k N b older a b) due
  have initial:Auth k (agateV (P 0) (Q 0)):=(hp 0 (by omega)).manor (hq 0 (by omega))
  have ender:Auth k (agateV (P n) (Q n)):=(hp n le_rfl).manor (hq n le_rfl)
  rw [tower R k N b older b (m+n) a _ ender home le_rfl (by omega) span,
      register R k N b older b n a _ _ home (by omega)
        (cruising R.draws R.hG R.green gate (by omega:m ≤ N) initial)
        (fun i hi=>cruising R.draws R.hG R.green (by omega:b ≤ m+i) (by omega:m+i ≤ N) (valid i hi)),
      tower R k N b older b m a _ initial home le_rfl gate (by omega)] at pulled
  refine pulled.trans (congrArg (_+·) (Finset.sum_congr rfl ?_))
  intro i hi
  have hi':=mem_range.mp hi
  exact tower R k N b older b (m+i) a _ (valid i hi') home le_rfl (by omega) (by omega)
end YM.Integration.WilsonSeparatedPrefixMovingPinHearing
