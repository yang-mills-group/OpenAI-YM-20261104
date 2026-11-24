import YM.Integration.WilsonAddressedPublicSelfCards
import YM.Integration.WilsonReflectedPublicStationFare
import YM.Next.UV_STRESS.Least
/-! On fixed physical reports the actual incoming public labels have a uniform bound on both ordered regulator tails. The original signed card and extracted representative are retained for every choice. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceOrderedRoster
open Function Filter Finset Extraction Spec Table Lattice RG Wilson Source OPE
open PhysicalNext.Repeat.Legato Trace.Terrace Next.UVStress Climb
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonThermometerUnitFilingFourSquare (Arm)
open WilsonReflectedPublicStationFare (station)
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}{order:Extraction.Order}{S:Table R.family.book}(F:Final R.family order S)
  {l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{arch:Arch R.family}{D T:ℕ}
  {I:Type}[Fintype I]{r:I→ℝ}(books:∀i,Book F (l:=l) H arch D T (r i))
  (grade:I→Fin (D+1))(name:∀i,Bool→S.Field (grade i).val)

def enrolled (i:I)(b:Bool):Arm R.family S (l:Filter _) (grade i).val (name i b):=
  ((books i).rows (grade i)).arm b (name i b)

abbrev raw (i:I)(b:Bool)(z:ℕ×ℕ):R.family.label (grade i).val:=
  (enrolled F books grade name i b).source z

include F in
theorem original:
    ∃first:ℕ,∃income:I→Bool→ℝ,
      (∀i b,1≤ income i b) ∧
      (∀N p, first≤ N → ∀i b,‖raw F books grade name i b (N,p)‖≤ income i b) ∧
      (∀i b,Tendsto (raw F books grade name i b) (l:Filter _) (𝓝 (enrolled F books grade name i b).label) ∧
        S.project (grade i).val (enrolled F books grade name i b).label=name i b) ∧
      order.late fun N p=>∀i b,Cards.PaidAt R.family.S N p
        (WilsonAddressedPublicSelfCards.width F (books i) (grade i) (name i b) b) (R.family.beta N p)
        (WilsonAddressedPublicSelfCards.fee F (books i) (grade i) (name i b) b)
        (R.family.O N p (raw F books grade name i b (N,p)) 0):=by
  classical
  let stationAt:=fun (i:I)(b:Bool)=>station F ((books i).rows (grade i)) b
  let price:=fun (i:I)(b:Bool)=>WilsonReflectedPublicStationFare.fee F ((books i).rows (grade i)) b (name i b)
  have issued (i:I)(b:Bool):R.family.ref (grade i).val≤ stationAt i b ∧ ∀N p,stationAt i b<N →
      quota R.family (grade i).val (stationAt i b) N p (raw F books grade name i b (N,p))≤
        R.family.S.a (stationAt i b)^(grade i).val*price i b:=
    WilsonReflectedPublicStationFare.original F ((books i).rows (grade i)) (books i).checked b (name i b)
  choose factor pos estimates using fun i b=>quota_stop R.family F.room.cutoff (issued i b).1
  let first:=((Finset.univ:Finset (I×Bool)).sup (fun a=>stationAt a.1 a.2))+1
  let income:=fun i b=>max 1 (factor i b*(R.family.S.a (stationAt i b)^(grade i).val*price i b))
  refine ⟨first,income,(fun i b=>le_max_left ..),?_,?_,?_⟩
  · intro N p late i b
    have before:stationAt i b<first:=Nat.lt_succ_of_le
      (Finset.le_sup (f:=fun a:I×Bool=>stationAt a.1 a.2) (Finset.mem_univ (i,b)))
    have live:=before.trans_le late
    exact (estimates i b N p _ live.le).trans ((mul_le_mul_of_nonneg_left ((issued i b).2 N p live) (pos i b)).trans (le_max_right ..))
  · exact fun i b=>⟨(enrolled F books grade name i b).approaches,(enrolled F books grade name i b).represents⟩
  · let pred:=fun z:ℕ×ℕ=>∀i b,Cards.PaidAt R.family.S z.1 z.2
        (WilsonAddressedPublicSelfCards.width F (books i) (grade i) (name i b) b) (R.family.beta z.1 z.2)
        (WilsonAddressedPublicSelfCards.fee F (books i) (grade i) (name i b) b)
        (R.family.O z.1 z.2 (raw F books grade name i b z) 0)
    apply (Extraction.Order.fused order pred).mp
    exact eventually_all.mpr fun i=>eventually_all.mpr fun b=>
      WilsonAddressedPublicSelfCards.original F (books i) (grade i) (name i b) b

end YM.Integration.WilsonMeasuredPublicEntranceOrderedRoster
end
