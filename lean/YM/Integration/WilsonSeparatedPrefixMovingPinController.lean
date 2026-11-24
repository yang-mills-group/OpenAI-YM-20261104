import YM.Integration.WilsonSeparatedPrefixMovingPinHearing
import YM.Integration.WilsonIndependentMatchedVacant

/-! A field reindexing admitted by the actual incoming spatial weight. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingPinController
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonSeparatedPrefixMovingPairSector (current)
open Finset
open scoped BigOperators Topology Classical

open WilsonPositionProgramPinnedHearthHistory (pin)
variable {G:Gauge}{e:ℕ}{E:Credit}

structure Sites (G:Gauge)(e u:ℕ) where
  part : ℕ → (Era G ℝ →+ Era G ℝ)
  authentic : ∀i k (X:Era G ℝ),Auth k X → Auth k (part i X)
  income : ∀i (X:Era G ℝ)(η A:ℝ),Flush e u η X A → Flush e u η (part i X) A

def appointed (G:Gauge)(e:ℕ)(S:Schedule)(b:ℕ)(a:Cover):Sites G e 0 where
  part:=fun i=>WilsonSeparatedPrefixMovingPinHearing.shiftHom (pin S b i a)
  authentic:=fun _ _ _ paid=>paid.shifted _
  income:=fun _ _ _ _ paid=>WilsonSeparatedPrefixMovingPinWallet.pinned paid _

def still (G:Gauge)(e u:ℕ):Sites G e u where
  part:=fun _=>AddMonoidHom.id _
  authentic:=fun _ _ _ h=>h
  income:=fun _ _ _ _ h=>h

def collected {u:ℕ}(R:Realm G (e+1) E)(V:Sites G e u)(k N i older:ℕ)(X:Era G ℝ):Era G ℝ:=
  cruises R.draws R.paid N k i older (V.part i X)

theorem earlier (G:Gauge)(k e u:ℕ)(E W:Credit):
    ∃C:Credit,∀(R:Realm G (e+1) E)(V:Sites G e u)(_room:Dormitory R k u W)(n m i N:ℕ)
      (_gate:R.anchor ≤ n)(_route:n ≤ m)(_edge:m ≤ i)(_stop:i ≤ N)(X:Era G ℝ)(_h:Auth k X)(amount:ℝ),
      Flush e u (paceT R.draws.S m i) X amount →
      ∀j ≤ e,∀ω:Fin 0→YForest G,‖(collected R V k N i n X).2 j 0 ω‖ ≤ 
        C.buy (WilsonSeparatedPrefixMovingCalendar.epoch R n i)*amount:=by
  obtain ⟨C,earn⟩:=WilsonSeparatedPrefixMovingWages.earlier G k e u E W
  refine ⟨C,?_⟩
  intro R V room n m i N gate route edge stop X auth cash paid
  exact earn R room n m i N gate route edge stop _ (V.authentic i k X auth) cash (V.income i X _ cash paid)

theorem vacant {u:ℕ}(R:Realm G (e+1) E)(V:Sites G e u)(m i N l r:ℕ)(hi:m ≤ i)(hn:i<N)
    (P Q:Era G ℝ)(miss:P=0 ∨ Q=0):
    collected R V (l+r) N i m (JoinGap R.draws R.paid i N l r P Q)=0:=by
  have none:=WilsonIndependentMatchedVacant.joined R i i N l r le_rfl hn P Q miss
  have old:=WilsonIndependentMatchedVacant.joined R m i N l r hi hn P Q miss
  rw [cruises_top] at none
  rw [collected,none,map_zero]
  simpa only [none] using old
end YM.Integration.WilsonSeparatedPrefixMovingPinController
