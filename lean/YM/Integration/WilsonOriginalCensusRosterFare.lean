import YM.Integration.WilsonOriginalCensusRosterMenu
import YM.Integration.WilsonIndependentCollarOrbitalUnweighted

/-! Sum the actual thermal and angular conditional on every named binder subset of one
    genuine original post. All the marker factors restore only the corresponding occupied slots. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusRosterFare
open Work.F08 WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Express WilsonCoeffUV.Wheel.Cadenza
open Function Filter Finset Lattice Wilson RG Precision Laurent WilsonCoeffUV Tree Bloch Exterior
open Next.Foundations PhysicalNext.Repeat.Legato
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer
open WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Bank.Realm
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Blue WilsonCoeffUV.Soil
open WilsonCoeffUV.Embroider WilsonCoeffUV.Winding WilsonCoeffUV.Bank.Ticket
open WilsonReceivedDatedVerseReprint WilsonReceivedCompactVerseEntrance
open WilsonMarkedIndependentPhysicalIntake WilsonMarkedIndependentMixedGeometry
open AnalyticNext.QuarticMatch.Sheets IndependentSourcePathFamily
open scoped Classical BigOperators

open Further.PhysicalPeriodLimitF933 Macrame Shingle FVA1Physical TwoReset
open WilsonOriginalRelativePageTail (retained)
open WilsonPointChildRelativeLift (centers)
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Blue
open WilsonNeutralTwoPrintPathPageLedger (price)
open WilsonNeutralTwoPrintPathRankFare (tariff)
open WilsonCoeffUV.Bank.Carp (plume)


open WilsonNeutralTwoPrintPathInheritedBlocks (gathered amount)
open WilsonOriginalCensusOrbitCenters (layout shifted)
open WilsonOriginalCensusDeckMean (mean)
open WilsonNeutralTwoPrintPathPageSeason (high)
open scoped Classical BigOperators
variable {G:Gauge}{e v:ℕ}{D k:Fin v→ℕ}{I:Type}[Fintype I][DecidableEq I]{H:I→ℕ}


open Filter WilsonCoeffUV.Winding
open scoped Topology


open WilsonReceivedFixedDigitCanonical (fixed)
open WilsonReceivedFixedDigitHistory (Digits)
open WilsonThermometerDeclaredSeeds OriginalMarkedSourceComet
open WilsonNeutralTwoPrintPathCalendar (spent)
open WilsonNeutralTwoPrintPathBoxMean (plotted)


open WilsonNeutralTwoPrintPathBoxPlacement (homes)
open WilsonNeutralTwoPrintPathBoxInk (ink)
open WilsonNeutralTwoPrintPathBoxHome (breadth)
open WilsonReceivedFixedDigitIntake (next)

open WilsonReceivedDepositedOrbitalFixedMoments (program reading)
open WilsonIndependentCollarOrbitalPeg (outer)
open WilsonIndependentCollarAngularPeg (multiplier)

open WilsonIndependentCollarOrbitalReception (relative)

open WilsonOriginalCensusRosterMenu (sheets central Paid)
open WilsonReceivedDepositedOrbitalNamedWage (wages)
open WilsonOriginalMixedBlockRows (room)
open WilsonOriginalCensusCompatibleCopies (entry)
open QuadraticLocal QuadraticLocal.Earn

/-- Finite sums keep the signed limit until the difference of readings has been taken. -/
private theorem addRows {A X:Type}[DecidableEq A]{F:Filter X}[NeBot F](s:Finset A)
    (weights:A→ℂ)(high:A→X→ℂ)(value:A→ℂ)(fee:A→ℝ)
    (checked:∀i∈s,Tendsto (high i) F (𝓝 (limUnder F (high i))) ∧ ‖limUnder F (high i)-value i‖ ≤ fee i):
    let total:=fun u=>∑i∈s,weights i*high i u
    Tendsto total F (𝓝 (limUnder F total)) ∧
      ‖limUnder F total-(∑i∈s,weights i*value i)‖ ≤ ∑i∈s,‖weights i‖*fee i:=by
  let limit:=∑i∈s,weights i*limUnder F (high i)
  have conv:Tendsto (fun u=>∑i∈s,weights i*high i u) F (𝓝 limit):=
    tendsto_finsetSum _ fun i hi=>tendsto_const_nhds.mul (checked i hi).1
  dsimp only
  rw [conv.limUnder_eq]
  refine ⟨conv,?_⟩
  dsimp only [limit]
  rw [←Finset.sum_sub_distrib]
  simp_rw [←mul_sub]
  calc
    _ ≤ ∑i∈s,‖weights i*(limUnder F (high i)-value i)‖:=norm_sum_le _ _
    _ ≤ _:=Finset.sum_le_sum fun i hi=>by rw [norm_mul];gcongr;exact (checked i hi).2

def whole (ranks:I→ℕ)(a:ℕ)(s:Finset I)(head:∀J:Finset I,J.Nonempty→J)
    (row:(J:Finset I)→J→ℕ→ℂ):ℂ:=
  if h:s.Nonempty then ∑r∈Finset.range (mass ranks s+a+1),row s (head s h) r else 0

/-- On every restricted subset use its actual head, its whole deposited word and all its
    diagonal ranks. The period gate supplied by the roster menu is uniform in this choice. -/
theorem original (R:Run G)(κ:(i:Fin v)→Knob (D i))(pt:Fin v→Chamber)
    (k:Fin v→ℕ)(N m K q per:ℕ)(words:I→Finset (Fin v))(front:I→Fin v)(C:Fin v→ℝ)
    (diameter maxRank a:ℕ)(ε:ℝ)(pos:0 ≤ ε)
    (paid:∀J:Finset I,∀o:J,∀r:Fin (maxRank+1),
      Paid (k:=k) R κ pt m K q per words front C diameter ε J o.val a r.val)
    (fitsRank:∀J:Finset I,mass (fun i=>mass k (words i)) J+a ≤ maxRank)
    (top:K ≤ N)(seed:(v:Fin v)→Choice R k v)(cells:Digits R.family.path.levels (Fin v))
    (sites:Fin v→ Cover)(t:Case D)(width:∀v,‖t v‖ ≤ C v)
    (grid:Side)(divides:(R.family.side m per).val∣grid.val)
    (digit:I→Site (loose R.family.path.levels m).L)
    (place:(J:Finset I)→J→I→ Cover)
    (fits:∀J:Finset I,∀o:J,breadth J o.val 0 (relative J o.val (place J o)) ≤ diameter)
    (Z:Stationary.Link G grid)(bound:‖Z‖ ≤ 1)
    {side:Side}{P:Earn.Passport side (Fin v)}(B:I→Earn.Binder P (Stock.census (Fin v)))
    (x:Affinity.Wallet (room (Fin v)))(target:(Stock.census (Fin v)).Mode)(head:∀J:Finset I,J.Nonempty→J):
    let Y:=fixed R k κ pt N K (m+1) cells seed
    let old:=program (k:=k) Y q words front (fun _=>sites) (fun _=>t)
    let ranks:=fun i=>mass k (words i)
    let h:=fun (s:Finset I)(o:s) r=>sheets R ranks N m q grid old digit s o.val (place s o) a r Z
    let c:=fun (s:Finset I)(o:s) r=>central R ranks N m q grid old digit s o.val (place s o) a r Z
    let full:=fun u=>∑s:Finset I,WilsonReceivedDepositedOrbitalNamedWage.wages B x target s*whole ranks a s head (fun s o r=>h s o r u)
    let expected:=∑s:Finset I,WilsonReceivedDepositedOrbitalNamedWage.wages B x target s*whole ranks a s head c
    let F:=coverFilter R.family.path.levels.S m grid
    Tendsto full F (𝓝 (limUnder F full)) ∧
      ‖limUnder F full-expected‖ ≤ (∑s:Finset I,‖WilsonReceivedDepositedOrbitalNamedWage.wages B x target s‖)*((maxRank+1)*ε) ∧
      ‖limUnder F full-expected‖ ≤ (2^Fintype.card I:ℝ)*(maxRank+1)*ε:=by
  intro Y old ranks h c full targetSum F
  letI:NeBot F:=coverFilter_neBot R.kit.floor m grid
  have rank (s:Finset I)(o:s)(r:ℕ)(hr:r∈Finset.range (mass ranks s+a+1)):
      Tendsto (h s o r) F (𝓝 (limUnder F (h s o r))) ∧ ‖limUnder F (h s o r)-c s o r‖ ≤ ε:=by
    have within:=fitsRank s
    have small:r < maxRank+1:=by change r∈Finset.range (mass (fun i=>mass k (words i)) s+a+1) at hr; rw [Finset.mem_range] at hr;omega
    exact paid s o ⟨r,small⟩ N top seed cells sites t width grid divides digit (place s o) (fits s o) Z bound
  let upper:=fun (s:Finset I) u=>whole ranks a s head (fun s o r=>h s o r u)
  let lower:=fun s=>whole ranks a s head c
  have each (s:Finset I):
      Tendsto (upper s) F (𝓝 (limUnder F (upper s))) ∧ ‖limUnder F (upper s)-lower s‖ ≤ (maxRank+1)*ε:=by
    by_cases occ:s.Nonempty
    · have part:=addRows (Finset.range (mass ranks s+a+1)) (fun _=>1) (h s (head s occ))
          (c s (head s occ)) (fun _=>ε) (rank s (head s occ))
      simp only [one_mul,norm_one,Finset.sum_const,Finset.card_range,nsmul_eq_mul] at part
      have coeff: ((mass ranks s+a+1:ℕ):ℝ) ≤ (maxRank:ℝ)+1:=by exact_mod_cast Nat.add_le_add_right (fitsRank s) 1
      simpa only [upper,lower,whole,dif_pos occ] using And.intro part.1 (part.2.trans (mul_le_mul_of_nonneg_right coeff pos))
    · have zero:limUnder F (fun _=> (0:ℂ))=0:=tendsto_const_nhds.limUnder_eq
      simpa [upper,lower,whole,occ,zero] using (show (Tendsto (fun _ : Covers R.family.path.levels.S m grid=> (0:ℂ)) F (𝓝 0)) ∧ (0:ℝ)≤(maxRank+1)*ε from ⟨tendsto_const_nhds,by positivity⟩)
  have total:=addRows (Finset.univ:Finset (Finset I)) (WilsonReceivedDepositedOrbitalNamedWage.wages B x target) upper lower
    (fun _=>(maxRank+1)*ε) (fun s _=>each s)
  have fare:=total.2
  rw [←Finset.sum_mul] at fare
  refine ⟨total.1,fare,fare.trans ?_⟩
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_right (WilsonIndependentCollarOrbitalUnweighted.disk B x target) (by positivity)

end YM.Integration.WilsonOriginalCensusRosterFare
end
