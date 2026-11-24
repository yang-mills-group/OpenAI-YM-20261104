import YM.Integration.WilsonMeasuredPublicEntranceNativeLowerLeft
import YM.Integration.WilsonMeasuredPublicEntranceNativeArrow

/-! Original two-point limits at possibly different engineering grades. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceNativeLowerMoment
open Function Filter Finset Set Lattice Wilson RG Source Cells GapsContact.Seams Trace.Terrace
open PhysicalNext.Repeat.Legato Extraction RG17 Spec Table Table.Pairing Climb Trace.Pilot PhysMS
open Maxwell Maxwell.Wick XSpace XSpace.Normalize XSpace.Structure1
open MS MS.Land MS.Menus MS.Theater Local.Physical
open PhysMS.Frame
open WilsonOriginalBlissMixedGram (grades)
open WilsonPhysicalStationLowerReceiver (ear pair evaluated)
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
local notation "D" => Table.Field (Bel R.family.book)

private theorem finite_rows {n:ℕ}{U:Fin n→Type}[∀j,NormedAddCommGroup (U j)][∀j,NormedSpace ℂ (U j)]
    [∀j,FiniteDimensional ℂ (U j)]{I:Type*}{l:Filter I}(A:I→MultilinearMap ℂ U ℂ)
    (B:MultilinearMap ℂ U ℂ)
    (rows:∀w,Tendsto (fun i=>A i w) l (𝓝 (B w)))
    {a:I→(j:Fin n)→U j}{b:(j:Fin n)→U j}(arms:∀j,Tendsto (fun i=>a i j) l (𝓝 (b j))):
    Tendsto (fun i=>A i (a i)) l (𝓝 (B b)):=by
  let P (j:Fin n):=Module.finBasis ℂ (U j)
  let K (j:Fin n):=Fin (Module.finrank ℂ (U j))
  have expand (X:MultilinearMap ℂ U ℂ)(v:(j:Fin n)→U j):
      X v=∑z:(j:Fin n)→K j,(∏j,(P j).coord (z j) (v j)) • X (fun j=>P j (z j)):=by
    have e:=X.map_sum (fun j (k:K j)=>(P j).repr (v j) k • P j k)
    have repr (j:Fin n):(∑k:K j,(P j).repr (v j) k • P j k)=v j:=(P j).sum_repr _
    rw [funext repr] at e
    rw [e]
    exact Finset.sum_congr rfl fun z _=>X.map_smul_univ _ _
  have co(z:(j:Fin n)→K j):Tendsto (fun i=>∏j,(P j).coord (z j) (a i j)) l (𝓝 (∏j,(P j).coord (z j) (b j))):=by
    apply tendsto_finsetProd
    intro j _
    exact (((P j).coord (z j)).continuous_of_finiteDimensional.tendsto _).comp (arms j)
  simpa only [←expand] using (tendsto_finsetSum Finset.univ
    fun (z:(j:Fin n)→K j) _=>(co z).smul (rows (fun j=>P j (z j))))

def ports {e h:ℕ}(v:D e)(z:D h):(i:Fin 2)→D (grades e h i):=
  Fin.cons (α:=fun i=>D (grades e h i)) v (fun _=>z)

def free {e h:ℕ}(y:Points 2)(v:D e)(z:D h):ℂ:=
  (Bel R.family.book).classMoment (Bel R.family.book) (grades e h) y (ports R v z)

theorem original {J:ℝ→tower S}(lead:Leading F J){I:Type*}{l:Filter I}{r:I→ℝ}
    (hr:Tendsto r l trail){x:I→Points 2}{y:Points 2}(hx:Tendsto x l (𝓝 y))(hy:y∈conf 2)
    {e h:ℕ}{X:I→S.Field e}{Y:I→S.Field h}{v:D e}{z:D h}
    (hv:Tendsto (fun i=>(J (r i) e).symm (X i)) l (𝓝 v))
    (hz:Tendsto (fun i=>(J (r i) h).symm (Y i)) l (𝓝 z)):
    Tendsto (fun i=>ear R (S:=S) (e:=e) (h:=h) (r i • x i) (Y i) (X i)) l (𝓝 (free R (e:=e) (h:=h) y v z)):=by
  let d:=grades e h
  let A (i:I):MultilinearMap ℂ (fun j:Fin 2=>D (d j)) ℂ:=
    (S.classMoment S d (r i • x i)).compLinearMap (fun j=>(J (r i) (d j)).toLinearMap)
  let M:MultilinearMap ℂ (fun j:Fin 2=>D (d j)) ℂ:=(Bel R.family.book).classMoment (Bel R.family.book) d y
  let b:=ports R v z
  let w (i:I):=ports R ((J (r i) e).symm (X i)) ((J (r i) h).symm (Y i))
  have fields (j:Fin 2):Tendsto (fun i=>w i j) l (𝓝 (b j)):=by
    fin_cases j
    · exact hv
    · exact hz
  have price:=finite_rows A M (fun row=>leading_at F lead (d:=d) row hr hx hy) fields
  change Tendsto (fun i=>A i (w i)) l (𝓝 (M b)) at price
  refine price.congr' (Filter.Eventually.of_forall fun i=>?_)
  change A i (w i)=ear R (S:=S) (r i • x i) (Y i) (X i)
  rw [evaluated R (S:=S) (r i • x i) (Y i) (X i)]
  change S.classMoment S d (r i • x i) (fun j=>(J (r i) (d j)) (w i j))=_
  congr 1
  funext j
  fin_cases j <;> exact LinearEquiv.apply_symm_apply _ _

end YM.Integration.WilsonMeasuredPublicEntranceNativeLowerMoment
end
