import YM.Integration.WilsonIndependentCollarOpticalPrint

/-! One polynomial charge for the complete optical itinerary, fixed before
the interval, the numerical dose, the original period and the fine cutoff. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonIndependentCollarOpticalCash
open Function Finset Lattice Wilson RG Precision
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Mer
open WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Cosmos
open WilsonReceivedFixedDigitHistory
open scoped Classical BigOperators
variable {G:Gauge} {ι:Type} [Fintype ι] [DecidableEq ι] {D k:ι→ℕ} {e:ℕ}

theorem envelope {s:Type} [Fintype s] [DecidableEq s] (f:s→Credit):
    ∃F:Credit,∀j Z,1≤Z → (f j).buy Z≤F.buy Z:=by
  have pick (A:Finset s):∃F:Credit,∀j∈A,∀Z,1≤Z → (f j).buy Z≤F.buy Z:=by
    induction A using Finset.induction_on with
    | empty=>exact ⟨Credit.unit,by simp⟩
    | @insert j A _ h=>
      obtain ⟨H,enrolled⟩:=h
      refine ⟨(f j).plus H,?_⟩;intro u hu Z hZ
      rcases Finset.mem_insert.mp hu with rfl|inA
      · exact Credit.thickens _ hZ
      · exact (enrolled u inA Z hZ).trans (Credit.thickened _ hZ)
  obtain ⟨F,atF⟩:=pick univ;exact ⟨F,fun i=>atF i (mem_univ i)⟩

theorem original (G:Gauge) (D k:ι→ℕ) (e:ℕ):
    ∃ P:Credit,∀(Q:Realm G (e+1) Credit.leanC),Cloze D k Q Credit.leanC →
    (∀S:Finset ι,Dormitory Q (mass k S) 0 Credit.leanC) →
    ∀(N:ℕ) (cell:Digits Q.draws ι) (Y:Outerm G D),Wellness k Y → ∀(m days:ℕ) (hm:Q.anchor≤ m),
      m+days≤N → ∀A Z:ℝ,0≤A → PadRank Q m (m+days) Z →
      (∀ y S, S.Nonempty → ∀f:Pen D S →L[ℝ] ℝ,‖f‖≤1 →
        Saturation e 0 0 (tuftV f (levelsO (Y y) S)).2 0 (A^S.card)) →
      (∀j (hj:Q.anchor≤ j), m ≤ j → j < m+days →
        2*elixir (Q.mint j hj).gear=3*(Q.mint j hj).σ) →
      Uniform Q Y (m+days) (by omega) A →
      Uniform Q (itinerary Q.draws Q.paid k N cell days m Y) m hm (P.buy Z*A):=by
  let c (S:Finset ι):=WilsonIndependentCollarOrdinaryAlgebra.cost e (mass k univ+e) S
  have cp (S:Finset ι):0≤c S:=zero_le_one.trans (WilsonIndependentCollarOrdinaryAlgebra.funded ..)
  let C:=1+∑S,c S
  have hc:1≤C:=le_add_of_nonneg_right (sum_nonneg fun j _=>cp j)
  have all (S:Finset ι):c S≤C:=(single_le_sum (fun i _=>cp i) (mem_univ S)).trans (by dsimp [C];linarith)
  let oneDate:=vigor G D k e Credit.leanC Credit.leanC
  obtain ⟨F,hF⟩:=envelope (fun S:Finset ι=>WilsonIndependentCollarOrdinaryWeak.price G (mass k S) e)
  let algebra:Credit:=⟨0,C,hc⟩
  let P:=(oneDate.powC 2).prodC (algebra.prodC F)
  refine ⟨P,?_⟩; intro Q sales dorm N cell Y well m days hm cut A Z hab room born inlet upper
  have hZ:1≤Z:=(Q.depth m hm).trans (room.year m le_rfl (by omega))
  have lt:1≤oneDate.buy Z:=oneDate.purchase hZ
  have ft:1≤F.buy Z:=F.purchase hZ
  have value:P.buy Z=oneDate.buy Z^2*(C*F.buy Z):=by rw [Credit.products,Credit.products,Credit.power];simp [algebra,Credit.buy]
  have eq:P.buy Z*A=oneDate.buy Z^2*(C*(F.buy Z*A)):=by rw [value];ring
  have wider:A≤oneDate.buy Z^2*(C*(F.buy Z*A)):=by rw [←eq];exact le_mul_of_one_le_left hab (P.purchase hZ)
  rw [eq]
  exact WilsonIndependentCollarOpticalOrdinary.original Q sales N cell Y well m days hm cut
    A C (F.buy Z) (oneDate.buy Z) Z hab hc ft lt room all (fun S=>hF S _ hZ) dorm born
    (fun i lower fine=>oneDate.elder (Q.depth _ (hm.trans lower)) (room.year i lower fine.le))
    inlet (fun y S=>shingled_pay (upper y S) hab wider)

end YM.Integration.WilsonIndependentCollarOpticalCash
end
