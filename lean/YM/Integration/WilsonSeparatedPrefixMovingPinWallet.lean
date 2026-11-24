import YM.Integration.WilsonSeparatedPrefixMovingWages
import YM.Integration.WilsonPositionProgramPinnedHearthHistory

/-! Translate a complete already joined deposit before its genuine older return. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingPinWallet
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile WilsonSeparatedPrefixMovingCalendar
open scoped BigOperators Topology Classical
variable {G:Gauge}{H:Hol G}{e u a:ℕ}{E W V:Credit}

theorem pinned {P:Era G ℝ}{e:ℕ}{η A:ℝ}(paid:Flush e 0 η P A)(a:Cover):
    Flush e 0 η (shifted P a) A:=by
  refine ⟨paid.1,?_⟩
  intro j hj r base
  have cost:=paid.2 j hj r base
  let move:dock Cover (Hooks G) r≃dock Cover (Hooks G) r:=
    Equiv.arrowCongr (Equiv.refl (Fin r)) (jog a)
  refine cap_walk _ _ move (fun x=>?_) cost
  change (1+η*_)^0*‖P.2 j r (jog (-a) ∘ move x)‖=(1+η*_)^0*‖P.2 j r x‖
  have same:jog (α:=Hooks G) (-a) ∘ move x=x:=by
    funext i;change (-(a)+(a+(x i).1),(x i).2)=x i
    rw [neg_add_cancel_left]
  rw [same,pow_zero,pow_zero]
theorem original (G:Gauge)(k e:ℕ)(E W:Credit):
    ∃C:Credit,∀(R:Realm G (e+1) E)(_room:Dormitory R k 0 W)(n m i N:ℕ)
      (_gate:R.anchor ≤ n)(_route:n ≤ m)(_edge:m ≤ i)(_stop:i ≤ N)(X:Era G ℝ)(_h:Auth k X)(amount:ℝ),
      Flush e 0 (paceT R.draws.S m i) X amount → ∀a:Cover,
      let returned:=cruises R.draws R.paid N k i n (shifted X a)
      ∀j ≤ e,∀ω:Fin 0→YForest G, ‖returned.2 j 0 ω‖ ≤ C.buy (epoch R n i)*amount:=by
  obtain ⟨C,earn⟩:=WilsonSeparatedPrefixMovingWages.earlier G k e 0 E W
  refine ⟨C,?_⟩
  intro R room n m i N gate route edge stop X auth cash paid a
  exact earn R room n m i N gate route edge stop (shifted X a) (auth.shifted a) cash (pinned paid a)
end YM.Integration.WilsonSeparatedPrefixMovingPinWallet
