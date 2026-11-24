import YM.Integration.WilsonMovingForkSharpUniform

set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkSharpNamedCapture
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonSeparatedPrefixMovingCalendar (epoch window)
open WilsonSeparatedPrefixMovingLateLaw (whole)
open WilsonSeparatedPrefixMovingWages (coupon)
open WilsonSeparatedPrefixMovingOwnDate (fee)
open WilsonCoeffUV.Cosmos.Polestar
open WilsonIndependentMovingRosterAllFineSeats (Elected Named)
open scoped BigOperators Topology Classical
local notation "C" => Credit.leanC
variable {G:Gauge}{h D k n height seats:ℕ}{H:Hol G}{F:Labels.Frame G h}{T:SectionData F}{p:h<D}

open MeasureTheory
open scoped SchwartzMap ContDiff
open WilsonSeparatedPrefixMovingJointSpectrum (Euclid)
open WilsonSeparatedPrefixMovingJointWaves (sheet)
open WilsonSeparatedPrefixMovingJointExpansion (coefficient angle)
open WilsonSeparatedPrefixMovingJointIntegral (signedRow)
open WilsonSeparatedPrefixMovingJointRows (bill)
open WilsonSeparatedPrefixMovingJointAddress (move)
open WilsonIndependentMatchedCoverProfile (word)
open WilsonMovingForkSharpMaster (Paid)
variable {a u e:ℕ}{v:Rails h k (u+a) e}
open WilsonSeparatedPrefixMovingRelativeMaster (Landed)
open WilsonMovingForkSharpUniform (Earned)
open WilsonSeparatedPrefixMovingSpectralSalary (salary)
theorem original (M:Master H)(p:h<D)(arms:Fin (n+1)→SealR G)(Q:SealR G)(a u e:ℕ)
    (v:Rails h k (u+a) e)(exterior:a=h+Q.h+k)(spare:0<k)(room:Q.h ≤ k)(covered:capP arms ≤ k)
    (entered:∀i,Named M height seats (arms i))(far:Named M height seats Q)
    (rank:capP arms+2 ≤ seats)(derivatives:u+a ≤ seats)
    (paint:Rarity D)(ψ χ:Rarity Q.D)(sm:ContDiff ℝ ∞ paint.ψ.val)(hψ:ContDiff ℝ ∞ ψ.ψ.val)(hχ:ContDiff ℝ ∞ χ.ψ.val)
    (collar:∀p q:Point4,paint.ψ.val p*ψ.ψ.val (q-p)=paint.ψ.val p*(χ.ψ.val q*ψ.ψ.val (q-p))):
    ∃S:𝓢(Euclid,ℂ),S=WilsonSeparatedPrefixMovingJointSpectrum.transformed ψ hψ ∧ (∀j:ℕ,Integrable (fun ξ:Euclid=>(1+‖ξ‖^j)*‖S ξ‖))∧
    ∃capture C₀ C₁ C₂:Credit,∀(torch:Torch H (M.T h) p v C C C)(choir:ChorusLine H (M.T h) p e C C C)
      (_same:choir.arch=torch.L),let R:=torch.L.V
      ∀(_sold:Elected M R height seats)(t s m N:ℕ),
      R.anchor ≤ t → t+s ≤ m → m ≤ N →
      ∀(φ:Wilt arms)(X:Herit arms)(B:Fin (n+1)→ℝ)(Z:ℝ),
      PadRank R (t+s) m Z → Bough arms φ (paceT R.draws.S m (t+s)) Z B →
      let genuine:=AutumnDay R.draws R.paid φ X m (t+s) N D
      ∃Y:CutsP H (M.T h) p v C C C C,
        Y.L=torch ∧ Y.L'=choir ∧ Y.vesselsC=R ∧ Y.N=N ∧ Y.m=t ∧ Y.i=s ∧ Y.pt=genuine ∧
        Y.fuel=max 0 (capture.buy Z*∏i,B i*fee (arms i) e (X i)) ∧
        Reports R.draws R.paid (M.T h) p φ X m (t+s) t N k=
          (paceT R.draws.S m (t+s))^h • steep R.draws R.paid (M.T h) p N (t+s) (m-(t+s)) Y.tileP ∧
        Y.springP s=genuine-Shrine Y.Ntop Y.tileP ∧ Paid Y Q C₀ C₁ C₂ ∧
        Landed Y m arms φ X Q paint ψ χ S ∧ Earned Y m arms φ X Q C₀ C₁ C₂ paint ψ χ S
          (Reports R.draws R.paid (M.T h) p φ X m (t+s) t N k) (salary paint χ sm hχ):=by
  obtain ⟨S,canonical,stock,join⟩:=WilsonSeparatedPrefixMovingChargedCapture.declared (H:=H) («C»:=C) (W:=C) (V:=C) (e:=e) Q paint ψ χ hψ hχ collar
  obtain ⟨capture,C₀,C₁,C₂,purchase⟩:=WilsonMovingForkSharpMaster.original M p arms Q a u e v exterior spare covered entered far rank derivatives
  refine ⟨S,canonical,stock,capture,C₀,C₁,C₂,?_⟩
  intro torch choir same R sold t s m N gate formed cut φ X B Z clock seatsNear genuine
  obtain ⟨roster,⟨external⟩⟩:=WilsonIndependentMovingRosterAllFineSeats.roster sold arms Q entered far
  obtain ⟨Y,hl,hv,realm,cutoff,first,span,actual,income,report,stable,paid⟩:=purchase torch choir same sold t s m N gate formed cut φ X B Z clock seatsNear
  have enrolled:PassportC H Y.vesselsC Q C C:=realm.symm ▸ external
  have seated:HorizonP H Y.vesselsC C C arms:=realm.symm ▸ roster
  have landed:Landed Y m arms φ X Q paint ψ χ S:=by
    have observed:Y.pt=AutumnDay Y.ax Y.tx φ X m Y.ceilC Y.N D:=by
      change Y.pt=AutumnDay Y.vesselsC.draws Y.vesselsC.paid φ X m (Y.m+Y.i) Y.N D
      rw [realm,first,span,cutoff]
      exact actual
    intro probe older order y o q r w
    dsimp only
    rw [observed]
    exact join Y.vesselsC enrolled (m:=m) arms seated φ X probe (Y.ha.trans (Nat.le_add_right ..)) order (Y.hc.trans Y.hn)
      (pace_le _ (Nat.le_add_right ..)) k covered h ((paceT Y.ax.S Y.m Y.ceilC)^h) y o q r w
  refine ⟨Y,hl,hv,realm,cutoff,first,span,actual,income,report,stable,paid,landed,?_⟩
  have date:Y.ceilC=t+s:=by change Y.m+Y.i=_;rw [first,span]
  apply WilsonMovingForkSharpUniform.original Y m arms φ X Q enrolled C₀ C₁ C₂ paid room (date.trans_le formed)
    (cut.trans_eq cutoff.symm) _ _ paint ψ χ sm hχ S stock landed
  change _=(paceT Y.vesselsC.draws.S m Y.ceilC)^h • steep Y.vesselsC.draws Y.vesselsC.paid _ _ Y.N Y.ceilC (m-Y.ceilC) Y.tileP
  rwa [realm,date,cutoff]
end YM.Integration.WilsonMovingForkSharpNamedCapture
