import YM.Integration.WilsonPositionProgramPublicStations
import YM.GapsContact.Earn.Buoys

/-! Numerical source income on the two already selected public Wilson columns. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedPublicStationFare
open Function Filter RG Source Wilson Labels Spec Table Extraction Climb
open MergeProof.East PhysicalNext.Repeat.Legato Next.UVStress Trace.Pilot OPE.Levy Further.CorrectedLift
open WilsonMeasuredPublicBank WilsonPositionProgramPublicStations GapsContact.Ascent
open scoped Topology Classical
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) {l : Ultrafilter (ℕ×ℕ)} {H : (Bel R.family.book).Hierarchy}
    {D d k : ℕ} {s r B : ℝ} {stock : Bank F l D s B} {cap : d ≤ D} {W : Vane R.family k}
    {fits : D ≤ k} {T : Spin.change S d}

def station (_A : Pair F stock cap W fits T r) (weak : Bool) : ℕ :=
  if weak then W.k else stock.j

def fee (_A : Pair F stock cap W fits T r) (weak : Bool) (v : S.Field d) : ℝ :=
  if weak then preExpense R.family d W.k W.b * ‖ladder R.family d (T.symm v)‖
  else B * cost F d s v

/-- The observed grade, coordinates and source in both branches remain those
of the appointed physical pair, for every cutoff above its own station. -/
theorem original (A : Pair F stock cap W fits T r) (issued : W.checked f H k)
    (weak : Bool) (v : S.Field d) :
    R.family.ref d ≤ station F A weak ∧ ∀ N p, station F A weak < N →
      quota R.family d (station F A weak) N p ((A.arm weak v).source (N,p)) ≤
        R.family.S.a (station F A weak)^d * fee F A weak v := by
  cases weak with
  | false =>
    let dept := stock.department d cap
    let L := dept.print v
    have atJ : L.j=stock.j := (dept.dated v).1
    refine ⟨by simpa only [station, Bool.false_eq_true, reduceIte, ←atJ] using L.owns,?_⟩
    intro N p live
    rw [A.pooled]
    have hn := L.numerical N p (atJ.symm ▸ live)
    rw [atJ] at hn
    exact hn
  | true =>
    let index : Fin (k+1) := ⟨d,Nat.lt_succ_of_le (cap.trans fits)⟩
    have old := issued.early index
    refine ⟨old,?_⟩
    intro N p live
    have seed := ((issued.rate N p live).1 index).1
    have priced := OPE.Levy.quotation R.family d W.k F.room.cutoff old live.le
      (W.R N p index) seed (ladder R.family d (T.symm v)) (b:=W.b)
    rw [A.weak]
    exact priced.trans_eq (mul_assoc ..)

end YM.Integration.WilsonReflectedPublicStationFare
end
