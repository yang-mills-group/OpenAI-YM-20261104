import YM.Integration.WilsonSeparatedPrefixMovingPinChamber
import YM.Integration.WilsonSeparatedPrefixMovingChargedCapture

/-! One actual Fourier spectrum, before the ultraviolet cutoff and the capture of the near roster. -/
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingPinFourier
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore MeasureTheory
open scoped BigOperators Topology Classical



open WilsonCoeffUV.Layout
open WilsonIndependentFittedExteriorProfile (home)
open WilsonIndependentMatchedCoverProfile (word)
variable {G:Gauge}{D:ℕ}



open Set
open scoped ContDiff
open WilsonSeparatedPrefixMovingAddressInk (writer)


open MeasureTheory Set
open scoped ContDiff
variable {Ω:Type*}[MeasurableSpace Ω]{μ:Measure Ω}
open WilsonSeparatedPrefixMovingJointSpectrum (Euclid)
open WilsonSeparatedPrefixMovingJointWaves (sheet wave)
open WilsonSeparatedPrefixMovingJointExpansion (angle coefficient coin)
open WilsonSeparatedPrefixMovingJointSpectrum (physical)
open WilsonSeparatedPrefixMovingJointIntegral (growth multiplier)
open scoped SchwartzMap
variable {E:ℕ}
open WilsonSeparatedPrefixMovingJointKernel (ink)
open WilsonSeparatedPrefixMovingJointKernelRead (painted)
open WilsonSeparatedPrefixMovingJointPages (field)
open WilsonSeparatedPrefixMovingJointIssued (originalScroll)

open WilsonSeparatedPrefixMovingJointFiledPages (cash)
open WilsonSeparatedPrefixMovingJointAddress (move)
variable {H:Hol G}{C W V:Credit}{e:ℕ}
open WilsonSeparatedPrefixMovingPinChamber (panel)
open WilsonSeparatedPrefixMovingPinSigned (slice)
open WilsonIndependentMovingRosterAllFineRead (Heard)

def waveRow (S:𝓢(Euclid,ℂ))(R:Realm G (e+1) C){n:ℕ}(Q:Fin (n+1)→SealR G)(F:SealR G)
    (α:Wilt Q)(φ:Rarity D)(χ:Rarity F.D)(X:Herit Q)(Z:F.Rider)(t m b older N K h:ℕ)
    (y:ℝ)(o:CellR)(q r:ℕ)(w:Fin r→YForest G)(ξ:Euclid):ℝ:=
  let ε:=paceT R.draws.S t b
  let near:=AutumnDay R.draws R.paid α X m b N D
  let outside:=fun d=>locale o (F.spins R.draws R.paid (sheet χ (angle ξ) d) t b N y Z)
  ∑c:Bool,∑d:Bool,coefficient (S ξ) c d*(cruises R.draws R.paid N (K+F.h) b older
    (agateV (word (ε^h • near) (sheet φ (angle ξ) c) ε y o h) (outside d))).2 q r w

theorem declared (F:SealR G)(φ:Rarity D)(ψ χ:Rarity F.D)(hψ:ContDiff ℝ ∞ ψ.ψ.val)(hχ:ContDiff ℝ ∞ χ.ψ.val)
    (window:∀p q:Point4,φ.ψ.val p*ψ.ψ.val (q-p)=φ.ψ.val p*(χ.ψ.val q*ψ.ψ.val (q-p))):
    ∃S:𝓢(Euclid,ℂ),S=WilsonSeparatedPrefixMovingJointSpectrum.transformed ψ hψ ∧
      (∀a:ℕ,Integrable (fun ξ:Euclid=>(1+‖ξ‖^a)*‖S ξ‖))∧
    ∀(R:Realm G (e+1) C)(_rf:PassportC H R F W V){n m t b N older:ℕ}(Q:Fin (n+1)→SealR G)
      (_rq:HorizonP H R W V Q)(α:Wilt Q)(X:Herit Q)(Z:F.Rider),R.anchor≤b→ older≤b→b≤N→ paceT R.draws.S t b≤1→
    ∀(K:ℕ)(_rank:capP Q≤K)(h:ℕ)(y:ℝ)(o:CellR),
    (∀(q r:ℕ)(w:Fin r→YForest G),Integrable (waveRow S R Q F α φ χ X Z t m b older N K h y o q r w)∧
      panel R Q F α ψ X Z φ y o t m b older N b q r w=∫ξ,waveRow S R Q F α φ χ X Z t m b older N K h y o q r w ξ)∧
    ∀(w0:Fin 0→YForest G)(target:ℕ)(A price:ℝ),Amplitude φ A→
      (∀(z:CellR)(s:Cover),Heard e target (paceT R.draws.S m t) price
        (fun q=>(slice R Q F α ψ X Z z (paceT R.draws.S m b) s t m b older N b N).2 q 0 w0))→
    Heard e target (paceT R.draws.S m t) ((5*radiusH φ (paceT R.draws.S t b) y)^4*A*price)
      (fun q=>panel R Q F α ψ X Z φ y o t m b older N N q 0 w0-∫ξ,waveRow S R Q F α φ χ X Z t m b older N K h y o q 0 w0 ξ):=by
  obtain ⟨S,idS,wealth,issued⟩:=WilsonSeparatedPrefixMovingChargedCapture.declared (H:=H) (C:=C) (W:=W) (V:=V) (e:=e) F φ ψ χ hψ hχ window
  refine ⟨S,idS,wealth,?_⟩
  intro R far n m t b N older Q near α X Z live past top small K hk h y o
  have receipt (q r:ℕ)(w:Fin r→YForest G):Integrable (waveRow S R Q F α φ χ X Z t m b older N K h y o q r w)∧
      panel R Q F α ψ X Z φ y o t m b older N b q r w=∫ξ,waveRow S R Q F α φ χ X Z t m b older N K h y o q r w ξ:=by
    have exactRow:=issued R far (m:=m) (t:=t) (b:=b) (older:=older) (N:=N) Q near α X Z live past top small K hk h ((paceT R.draws.S t b)^h) y o q r w
    exact ⟨exactRow.1,(WilsonSeparatedPrefixMovingPinChamber.captured R Q F near far α ψ X Z φ y o t m b older N h q r w live past top).trans exactRow.2⟩
  refine ⟨receipt,?_⟩
  intro w0 target A price amp sale
  have cmp:=WilsonSeparatedPrefixMovingPinChamber.original R Q F near far α ψ X Z φ y o t m b older N target w0 live past top small A price amp sale
  simpa only [←(receipt _ 0 w0).2] using cmp
end YM.Integration.WilsonSeparatedPrefixMovingPinFourier
