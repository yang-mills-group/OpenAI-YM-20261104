import YM.Integration.WilsonMovingForkSharpBudget
import YM.Integration.WilsonMovingForkSharpGrades
import YM.Integration.WilsonMovingForkSharpNamedCapture

set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkSharpRetainedBook
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
open WilsonCoeffUV.Mer.Patrol (BayV)
open RegulatorIR RegulatorIR.Ledger
variable {D' j extra:ℕ}
open WilsonMovingForkSharpUniform (Earned)
open WilsonSeparatedPrefixMovingSpectralSalary (salary)
def Booked (Y:CutsP H T p v C C C C)(m:ℕ)(arms:Fin (n+1) → SealR G)(α:Wilt arms)(X:Herit arms)
    (Q:SealR G)(C₀ C₁ C₂ ledger pay thermal:Credit)(u':ℕ)(x:Verse F):Prop:=
  ∀(φ:Rarity D)(ψ χ:Rarity Q.D)(hφ:ContDiff ℝ ∞ φ.ψ.val)(hψ:ContDiff ℝ ∞ ψ.ψ.val)(hχ:ContDiff ℝ ∞ χ.ψ.val),
  (∀p q:Point4,φ.ψ.val p*ψ.ψ.val (q-p)=φ.ψ.val p*(χ.ψ.val q*ψ.ψ.val (q-p)))  → 
  let S:=WilsonSeparatedPrefixMovingJointSpectrum.transformed ψ hψ
  (∀j:ℕ,Integrable (fun ξ:Euclid=>(1+‖ξ‖^j)*‖S ξ‖)) ∧ Landed Y m arms α X Q φ ψ χ S ∧
    WilsonMovingForkSharpBudget.Earned Y m arms α X Q C₀ C₁ C₂ ledger pay thermal u' φ ψ χ S x (salary φ χ hφ hχ) ∧
    WilsonMovingForkSharpGrades.Audited Y m arms α X Q C₀ C₁ C₂ ledger pay thermal u' φ ψ χ S x (salary φ χ hφ hχ)

theorem original (p:h<D)(T:SectionData F)(Q:SealR G)(v:Rails h k (u+a) e)(u':ℕ):
  ∃ledger pay thermal:Credit,∀(Y:CutsP H T p v C C C C),
    SpringD Y.vesselsC (h+Q.h) u' (Q.h+h+(u'+(h+1)+2)) C  →  Dormitory Y.vesselsC (h+Q.h) u' C  → 
    ∀(m:ℕ)(arms:Fin (n+1) → SealR G)(α:Wilt arms)(X:Herit arms)(_ticket:PassportC H Y.vesselsC Q C C)
    (_seated:HorizonP H Y.vesselsC C C arms)(C₀ C₁ C₂:Credit)(_paid:Paid Y Q C₀ C₁ C₂)
    (_room:Q.h ≤ k)(_covered:capP arms ≤ k)(_formed:Y.ceilC ≤ m)(_cut:m ≤ Y.N)
    (x:Verse F)(_report:x=(paceT Y.ax.S m Y.ceilC)^h • steep Y.ax Y.tx T p Y.N Y.ceilC (m-Y.ceilC) Y.tileP)
    (_genuine:Y.pt=AutumnDay Y.ax Y.tx α X m Y.ceilC Y.N D),
      Booked Y m arms α X Q C₀ C₁ C₂ ledger pay thermal u' x:=by
  obtain ⟨ledger,pay,thermal,money⟩:=WilsonMovingForkSharpBudget.original (H:=H) (n:=n) p T Q v u'
  refine ⟨ledger,pay,thermal,?_⟩
  intro Y spring dorm m arms α X ticket seated C₀ C₁ C₂ paid room covered formed cut x report seen φ ψ χ hφ hψ hχ collar S
  obtain ⟨_,rfl,stock,join⟩:=WilsonSeparatedPrefixMovingChargedCapture.declared (H:=H) («C»:=C) (W:=C) (V:=C) (e:=e) Q φ ψ χ hψ hχ collar
  have landed:Landed Y m arms α X Q φ ψ χ S:=by
    intro probe older order y o q r w
    dsimp only
    rw [seen]
    exact join Y.vesselsC ticket (m:=m) arms seated α X probe (Y.ha.trans (Nat.le_add_right ..)) order (Y.hc.trans Y.hn)
      (pace_le _ (Nat.le_add_right ..)) k covered h ((paceT Y.ax.S Y.m Y.ceilC)^h) y o q r w
  have bought:=money Y spring dorm m arms α X ticket C₀ C₁ C₂ paid room formed cut x report φ ψ χ hφ hχ S stock landed
  exact ⟨stock,landed,bought,WilsonMovingForkSharpGrades.original Y m arms α X Q C₀ C₁ C₂ ledger pay thermal u' φ ψ χ S x _ bought⟩
end YM.Integration.WilsonMovingForkSharpRetainedBook
