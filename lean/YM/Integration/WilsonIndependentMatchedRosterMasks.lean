import YM.Integration.WilsonIndependentMatchedTotalTop
import YM.Integration.WilsonIndependentMatchedRosterChronology

/-! The sum over stable and fitted choices is taken inside the one ordinary
product. Only after this equality can it pass through the normalized course. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedRosterMasks
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile
open scoped BigOperators Topology Classical

open WilsonIndependentMatchedCoverProfile
variable {G:Gauge}{n:ℕ}

def Bits : ℕ→Type
  | 0=>Bool
  | n+1=>Bool×Bits n

instance finite : (n:ℕ)→Fintype (Bits n)
  | 0=>inferInstanceAs (Fintype Bool)
  | n+1=>@instFintypeProd Bool (Bits n) inferInstance (finite n)

def choose : (n:ℕ)→Bits n→Fin (n+1)→Bool
  | 0,m,_=>m
  | n+1,m,s=>Fin.cases (motive:=fun _=>Bool) m.1 (choose n m.2) s

def quiet : (n:ℕ)→Bits n
  | 0=>false
  | n+1=>(false,quiet n)

lemma empty (n:ℕ)(s:Fin (n+1)):choose n (quiet n) s=false:=by
  induction n with
  | zero=>rfl
  | succ n ih=>exact Fin.cases rfl (fun j=>ih j) s

lemma present (n:ℕ)(m:Bits n)(h:m ≠ quiet n):∃s,choose n m s=true:=by
  induction n with
  | zero=> by_cases q:m=true
           · exact ⟨0,q⟩
           · exact (h (by cases m <;> simp_all [quiet])).elim
  | succ n ih=>
    rcases m with ⟨b,q⟩
    cases b
    · obtain ⟨s,hs⟩:=ih q (fun eq=>h (by rw [eq];rfl))
      exact ⟨s.succ,hs⟩
    · exact ⟨0,rfl⟩

def placed (P Q:Fin (n+1)→Era G ℝ)(m:Bits n):Era G ℝ:=
  MassP G ℝ n (fun s=>if choose n m s then P s else Q s)

private def paired (P:Era G ℝ):Era G ℝ→+Era G ℝ where
  toFun:=agateV P
  map_zero':=Prod.ext (funext fun _=>(woadNull _).1) (woadNull _).1
  map_add' Q T:=(WilsonIndependentMatchedTotalTop.binary Q T P).2

theorem deposited (n:ℕ)(P Q:Fin (n+1)→Era G ℝ):
    MassP G ℝ n (fun s=>P s+Q s)=∑m:Bits n,placed P Q m:=by
  induction n with
  | zero=>
    change P 0+Q 0=∑m:Bool,if m then P 0 else Q 0
    simp
  | succ n ih=>
    change agateV (P 0+Q 0) (MassP G ℝ n (fun s=>P s.succ+Q s.succ))=
      ∑m:Bool×Bits n,agateV (if m.1 then P 0 else Q 0) (placed (Fin.tail P) (Fin.tail Q) m.2)
    rw [ih (fun s=>P s.succ) (fun s=>Q s.succ),(WilsonIndependentMatchedTotalTop.binary ..).1,
      Fintype.sum_prod_type,Fintype.sum_bool]
    simp only [if_true,Bool.false_eq_true,if_false]
    change paired (P 0) (∑m:Bits n,placed _ _ m)+paired (Q 0) (∑m:Bits n,placed _ _ m)=_
    simp only [map_sum,paired,AddMonoidHom.coe_mk,ZeroHom.coe_mk]
    abel

theorem fitted (P Q:Fin (n+1)→Era G ℝ):placed P Q (quiet n)=MassP G ℝ n Q:=by
  simp only [placed,empty,Bool.false_eq_true,if_false]

end YM.Integration.WilsonIndependentMatchedRosterMasks
