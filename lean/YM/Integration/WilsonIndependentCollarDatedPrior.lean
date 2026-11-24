import YM.Integration.WilsonIndependentCollarOutputFilm
import YM.Integration.WilsonIndependentCollarPointBill
import YM.Integration.WilsonReceivedFixedDigitCanonical

/-! The actual predecessor sewn into the dated census is the original
fixed-K canonical word at each physical child and at the original cutoff. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.Integration.WilsonIndependentCollarDatedPrior
open Function Finset Lattice RG Wilson Precision PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Bank WilsonCoeffUV.Cosmos WilsonCoeffUV.Blue WilsonCoeffUV.Embroider WilsonCoeffUV.Winding
open WilsonReceivedFixedDigitHistory FundedMarkedPathSelection WilsonReceivedCanonicalVerseBasis
open WilsonThermometerDeclaredSeeds
open WilsonReceivedCanonicalVerseRegister (start)
open WilsonReceivedFixedDigitCanonical (fixed)
open scoped Classical BigOperators
variable {G:Gauge}{n q:ℕ}{k D:Fin n→ℕ}

def onLevels {G':Gauge}{ι:Type}{L L':Levels G'}(same:L=L')(cells:Digits L ι):Digits L' ι:=
  same ▸ cells

private theorem rep {L L':Levels G}{O O':ChartRatio G}(same:L=L')(chart:O=O')
    (N:ℕ)(cells:Digits L (Fin n))(d m:ℕ)(Y:Outerm G D):
    itinerary L O k N cells d m Y=itinerary L' O' k N (onLevels same cells) d m Y:=by
  subst L' O';rfl

variable (R:Run G)(V:Realm G (q+1) Credit.leanC)(j:ℕ)(hj:V.anchor ≤ j)
  (S:Finset (Fin n))(N K:ℕ)(top:K≤N)(upper:j+1≤K)
  (cells:Digits V.draws (Fin n))(κ:(l:Fin n)→Knob (D l))(pt:Fin n→Chamber)(seed:(l:Fin n)→Choice R k l)
  (A:ℝ)(wallet:Uniform V (itinerary V.draws V.paid k N cells (K-(j+1)) (j+1) (start R k κ pt seed))
    (j+1) (by omega) A)

def inlet:Input V hj S k D A:=
  let healthy:Wellness k (start R k κ pt seed):=by
    obtain ⟨_,_,initial⟩:=WilsonIndependentCollarPointBill.original R D k 0 (w:=1) zero_lt_one
    exact (initial κ pt seed).1
  WilsonIndependentCollarOutputFilm.atChild V j hj S k N (K-(j+1)) cells (start R k κ pt seed)
    healthy (by omega) A wallet

theorem original (draw:V.draws=R.family.path.levels)(chart:V.paid=R.metals.O)(y:Fin n → Cover)(J:Finset (Fin n)):
    output (inlet R V j hj S N K top upper cells κ pt seed A wallet) J N y =
      fixed R k κ pt N K j (onLevels draw cells) seed y J:=by
  change itinerary V.draws V.paid k N cells (K-(j+1)+1) j (start R k κ pt seed) y J=
    itinerary R.family.path.levels R.metals.O k N (onLevels draw cells) (K-j) j (start R k κ pt seed) y J
  have count:K-(j+1)+1=K-j:=by omega
  rw [count]
  exact congrFun (congrFun (rep draw chart N cells (K-j) j (start R k κ pt seed)) y) J

end YM.Integration.WilsonIndependentCollarDatedPrior
end
