import YM.Integration.WilsonIndependentCollarOpticalCash
import YM.Integration.WilsonIndependentCollarSeedTariff
import YM.Integration.WilsonReceivedCanonicalVerseRegister

/-! One whole-collar credit for the actual canonical finite Wilson trial.
The source index and every later inlet and child are chosen after the tariff. -/
set_option autoImplicit false
set_option maxHeartbeats 230000
noncomputable section
namespace YM.Integration.WilsonIndependentCollarOpticalTrial
open Function Finset Lattice Laurent Wilson RG Source Labels Precision PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Mer
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Blue WilsonCoeffUV.Cosmos WilsonCoeffUV.Embroider
open WilsonReceivedFixedDigitHistory WilsonReceivedCanonicalVerseBasis
open IndependentSourcePathFamily OriginalMarkedSourceComet WilsonThermometerDeclaredSeeds
open WilsonOriginalStarSceneWords
open scoped Classical BigOperators
variable {G:Gauge} {ι:Type} [Fintype ι] [DecidableEq ι]

theorem tariff (G:Gauge) (D k:ι→ℕ) (e:ℕ):
    ∃ P:Credit,∀(V:Realm G (e+1) Credit.leanC),Cloze D k V Credit.leanC →
      (∀S:Finset ι,Dormitory V (mass k S) 0 Credit.leanC) →
    ∀(N:ℕ) (cell:Digits V.draws ι) (Y:Outerm G D),Wellness k Y →
    ∀(m days:ℕ)(hm:V.anchor≤ m),m+days≤N → ∀ A Z:ℝ,0≤A → PadRank V m (m+days) Z →
      (∀y S,shingled y S Y e 1 A) → Uniform V Y (m+days) (by omega) A →
      (∀ j (hj:V.anchor≤j),m ≤ j → j < m+days → 2*elixir (V.mint j hj).gear=3*(V.mint j hj).σ) →
      Uniform V (itinerary V.draws V.paid k N cell days m Y) m hm (P.buy Z*A):=by
  obtain ⟨F,hF⟩:=WilsonIndependentCollarOpticalCash.original G D k e
  obtain ⟨C,one,seed⟩:=WilsonIndependentCollarSeedTariff.original G D k e
  let fixed:Credit:=⟨0,C,one⟩
  refine ⟨F.prodC fixed,?_⟩
  intro V sales dorm N cell Y well m days hm cut A Z non room shing upper widths
  have price:(F.prodC fixed).buy Z*A=F.buy Z*(C*A):=by rw [Credit.products];simp [fixed,Credit.buy,mul_assoc]
  rw [price]
  exact hF V sales dorm N cell Y well m days hm cut (C*A) Z (mul_nonneg (zero_le_one.trans one) non)
    room (seed Y well A non shing) widths (fun y S=>shingled_pay (upper y S) non (le_mul_of_one_le_left non one))

theorem original (R:Run G) (D k:ι→ℕ) (κ:(j:ι)→Knob (D j)) (pt:ι→Chamber) (e:ℕ):
    ∃P:Credit,∃B:ℝ,1≤B ∧ ∀(V:Realm G (e+1) Credit.leanC),Cloze D k V Credit.leanC →
      (∀S:Finset ι,Dormitory V (mass k S) 0 Credit.leanC) →
    ∀(N:ℕ)(cell:Digits V.draws ι) (q:(j:ι)→Choice R k j) (m days:ℕ) (hm:V.anchor ≤ m),
      m+days≤N → (V.mint (m+days) (by omega)).σ≤1 → ∀Z:ℝ,PadRank V m (m+days) Z →
      (∀ j (hj:V.anchor≤j),m ≤ j → j < m+days → 2*elixir (V.mint j hj).gear=3*(V.mint j hj).σ) →
      Uniform V (itinerary V.draws V.paid k N cell days m (WilsonReceivedCanonicalVerseRegister.start R k κ pt q))
        m hm (P.buy Z*B):=by
  obtain ⟨P,rates⟩:=tariff G D k e
  obtain ⟨B,one,plan⟩:=WilsonReceivedCanonicalVerseRegister.original R k κ pt e (s:=1) zero_lt_one
  refine ⟨P,B,one,?_⟩
  intro V sale dorm N cell q m days hm top width Z room widths
  obtain ⟨good,entry,_⟩:=plan q
  exact rates V sale dorm N cell _ good m days hm top B Z (zero_le_one.trans one) room entry
    (fun y S i h r=>(entry y S i h r).shave width) widths

end YM.Integration.WilsonIndependentCollarOpticalTrial
end
