import YM.Integration.WilsonPosteriorProjectionPaidWord
import YM.Integration.FVA1Physical.Round2.PhysicalFieldWords

/-! The genuine field word at a separately selected common audit order. All inputs, forest and independent emitted coefficient still belong to that same realized scene. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPosteriorProjectionCommonWords
open Function Filter Finset Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open PhysicalNext PhysicalNext.Repeat JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open PhysicalNext.Repeat.Legato Cub Circlet Graces Roost Qlocal.Schedule
open YM.Integration.FVA1Physical.Wilson RGComparison.Core16.Spool MSbar MSbar.Heath MSbar.Heath.Stock
open MSbar.Midpoint MSbar.Cacao MSbar.CrossH MSbar.Bakery.Film MSbar.Whisk MSbar.Rolling MSbar.Kelvin MSbar.Lis MSbar.Bulk
open Tree Pressure Push.Uniform Exterior
open MSbar.Mosaic
open scoped Classical Topology BigOperators
open YM.Integration.FVA1Physical.Round2.Curvature
variable {G : Gauge} {ι : Type} [Fintype ι] (J : ι → Lamp G)

def AtOrder (R : PhysicalNext.Repeat.Legato.Run G) (u : G.ColorIndex) (p q L : ℕ)
    (D η : ℝ) (m : ℕ) : Prop :=
    ∀ᶠ k:ℕ in atTop, ∀ N n,k ≤ N → 
      (∃ S:Scene R.family.path.levels n (m+2),Realized R.alloy.B.kin N n k (m+2) (Lis.sun G u) S) ∧
      ∀ (S:Scene R.family.path.levels n (m+2)) (scene:Realized R.alloy.B.kin N n k (m+2) (Lis.sun G u) S)
        (j:ℕ) (kj:k ≤ j) (jN:j < N),
        let F:=(scene.step j jN kj).choose
        let v:=(scene.step j jN kj).choose_spec.choose
        let A:=sceneIssue (N:=N) (RunFormalChain.fromRun R) S F v
        let y:=R.family.path.levels.clock.hatBeta (j+1)
        S.Poly j=A.Zpost R.metals.O ∧
          ∀ (b:Site A.c) (z:Positions (Primary A.c G)),‖z‖ ≤ D → 
            ∀ (o:ι → Site A.f), (∀ t:Slice J,separation (A.S.ratio.embed b) (legs J o t).1 ≤ L*closeN y) → 
            ∀ (part:Bool) (l:List (Primary A.c G)),l.length = q → 
              let Q:=renderedPolynomial (emittedRows A R.metals.O (jointFieldBank J A o part) p) p A.fClock
              |buoy (fun w=>expect A.S A.pre (postcard G A.c A.fClock w) (fun U=>look part (tally J o U))
                -clue Q w) z l| ≤ A.fClock^((p:ℝ)+1-η)

theorem word (hG:G.Simple) (R:PhysicalNext.Repeat.Legato.Run G) (u:G.ColorIndex)
    (inputs:PinnedReadings J R u) (emissions:PinnedEmissions J R u) (p q s L : ℕ) (hs : 6 ≤ s)
    (D η : ℝ) (hD : 0 ≤ D) (hη : 0 < η) (a : ℕ) (adequate : chartInversePower (q+1)+(p+1) ≤ a) :
    AtOrder J R u p q L D η (p+1+a*q) := by
  let m:=p+1+a*q
  let C:=fieldWordConstant (q+1) q (Nat.lt_succ_self q)
  let d:=1+a*q
  obtain ⟨hδ,clock⟩:=derivative_clock p C d (Nat.cast_nonneg _) hη
  obtain ⟨t,convert⟩:=eventually_atTop.mp clock
  let M:=max 2 (max t (chartOrderPrice G |R.family.path.levels.clock.kernel.penalty| (q+1) q (stencilBound J)+((m+1:ℕ):ℝ)))
  have grows:=Multi.Wage.hat_tend hG R.family.path.levels
  obtain ⟨k₀,big⟩:=eventually_atTop.mp (grows.eventually_ge_atTop (2*M))
  have hp:0 < D+1:=by linarith only [hD]
  have clockSmall:=actual_clock_small R.family.path (q:=1) zero_lt_one (lt_min zero_lt_one (inv_pos.mpr hp)) hG R.T.choice
  filter_upwards [inputs m s L hs (D+1) 1 hp.le zero_lt_one,
    emissions m (m+2) s (q+1) L (by omega) hs (D+1) (rowExponent η) hp.le hδ,
    clockSmall,eventually_ge_atTop k₀] with k points rows small cut N n kn
  obtain ⟨existsScene,values⟩:=points N n kn
  refine ⟨existsScene,?_⟩
  intro S scene j kj jN
  let Z:=RunFormalChain.fromRun R
  let F:=(scene.step j jN kj).choose
  let v:=(scene.step j jN kj).choose_spec.choose
  let A:=sceneIssue (N:=N) Z S F v
  let x:=R.family.path.levels.clock.hatBeta j
  let y:=R.family.path.levels.clock.hatBeta (j+1)
  have je:=kj.trans (Nat.le_succ j)
  obtain ⟨realized,bill⟩:=values S scene j kj jN
  refine ⟨realized,?_⟩
  have tr:=(scene.budget (j+1) jN je).1
  have co:=R.T.choice.represents N n (j+1) jN
  have band:y/2 ≤ A.pre.beta:=co.band.1
  have height:2*M ≤ y:=big (j+1) (cut.trans je)
  have large:M ≤ A.pre.beta:=by linarith only [band,height]
  have base:1 ≤ A.pre.beta:=(one_le_two.trans (le_max_left ..)).trans large
  have tβ:t ≤ A.pre.beta:=((le_max_left ..).trans (le_max_right ..)).trans large
  have above:0 < A.fClock:=inv_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans_le base))
  have smaller:=small (j+1) je N n jN
  change A.fClock^(1:ℝ) ≤ min 1 (D+1)⁻¹ at smaller
  rw [Real.rpow_one] at smaller
  have unit:=smaller.trans (min_le_left ..)
  have room:A.fClock*(D+1) ≤ 1:=(le_div_iff₀ hp).mp (by simpa only [one_div] using smaller.trans (min_le_right ..))
  have past:x ≤ y:=WilsonBulk.Parapet.Agenda.hat_mobile R.family.path.levels hG (Nat.le_succ j)
  have fee:=convert A.pre.beta tβ x (R.family.path.levels.fits.delayed j).le (by linarith only [past,band])
  have branch: A.S.patch.Branches A.S.kernel G:=(R.family.path.levels.blocks j n).branches
  have prem:Premier (main A.f A.pre.clip A.pre.path):=by
    change Premier (main _ (R.family.path.rep N n (j+1)).clip (R.family.path.rep N n (j+1)).path)
    rw [Z.clips N n (j+1) jN,Z.selected N n (j+1) jN];exact tr.quiet
  have crit:Critical A.F A.pre.clip A.pre.path A.ρ:=by
    change Critical F (R.family.path.rep N n (j+1)).clip (R.family.path.rep N n (j+1)).path _
    rw [Z.clips N n (j+1) jN,Z.selected N n (j+1) jN];exact (Z.planned.critical N j n jN F).1
  have pd:(mold A.pre A.F A.v).PosDef:=by
    change (Push.Uniform.block (priced F v (R.family.path.rep N n (j+1)).clip (R.family.path.rep N n (j+1)).path) 0).PosDef
    rw [Z.clips N n (j+1) jN,Z.selected N n (j+1) jN]
    exact blueprint F v (Z.kin.path N (j+1)) _ branch tr.quiet (Z.post.price _) (Z.planned.gap N j n jN F)
  have hα:0 ≤ Mosaic.αm x:=by unfold Mosaic.αm Mosaic.hatW Alto.flurry;positivity
  intro b z hz o near part l length
  have row:=((rows N n kn).2 S scene j kj jN)
  have hefty:chartOrderPrice G |A.S.kernel.penalty| (q+1) q (stencilBound J)+((m+1:ℕ):ℝ) ≤ A.pre.beta:=
    ((le_max_right ..).trans (le_max_right ..)).trans large
  have bound:=WilsonPosteriorProjectionPaidWord.priced J A R.metals.O tr.bond branch prem crit pd (A.pre.envelope co.good)
    (SectorNext.Vacuum.strictly R.family.path R.T.choice N n (j+1) jN)
    o part b z l p s L a (by simpa only [length] using adequate) hα hz above unit room near base fee.1 (by simpa only [length] using hefty)
    (fun w hw=>by simpa only [length] using bill (A.S.ratio.embed b) w hw part)
    (fun w hw i hi=>by rw [length] at hi ⊢;exact row b w hw o near part i hi)
  have final : (C+(d:ℝ)*x^(rowExponent η))*A.fClock^(p+1) ≤ A.fClock^((p:ℝ)+1-η) := fee.2
  apply bound.trans
  rw [length]
  exact final


end YM.Integration.WilsonPosteriorProjectionCommonWords
end

