import YM.Integration.WilsonMacroscopicRichWatchReader
import YM.Integration.FilteredWilsonProduct

/-! The measured finite detector uses the very same physical spectator insertions on the same torus. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichWatchPlot
open Set Function Filter MeasureTheory Spec OPE OPE.Orbits PhysMS Lattice Cells Wilson
open Next.UVStress StressFlux.Matching WilsonMacroscopicRichWatchReader
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{S:Table C.book}{f:Extraction.Order}

def calibrated (S:Table C.book)(W:Watch C):Watch C:={W with
  q:=fun i=>detectorRaw S (S.classTokens (W.q i))}

theorem invariant (S:Table C.book)(W:Watch C)(h:ℕ):
    (calibrated S W).tester S h=W.tester S h:=by
  have hq:S.classTokens ∘ (calibrated S W).q=S.classTokens ∘ W.q:=by
    funext i
    exact raw_class _ _
  unfold Watch.tester
  rw [hq]
  rfl

def index (S:Table C.book)(W:Watch C):Fin W.n≃Fin (exterior S W).length:=
  finCongr (by simp [exterior,classes])

theorem entry (W:Watch C)(i:Fin W.n):
    (exterior S W).get (index S W i)=(W.held i.succ,S.classTokens (W.q i)):=by
  unfold exterior classes
  rw [List.get_ofFn]
  rfl

theorem grid (k N p:ℕ)(live:k≤N)(x:Cover):
    ceilSite C N p (C.S.gridPoint k x)=location C.S k N p x:=by
  have zero:ceilSite C N p (0:E4)=0:=by
    change Lattice.wrap _ (fun _=>⌈(0:ℝ)/C.S.a N⌉)=0
    simp only [zero_div,Int.ceil_zero]
    exact (Lattice.wrap _).map_zero
  simpa only [zero_add,zero] using
    WilsonExteriorGeometry.ceilSite_add_grid (C:=C) (p:=p) live (0:E4) x

theorem original {a h:ℕ}(W:Fin a→Watch C)(D:(Fin a→ℂ)→L[ℂ]S.Field h)
    (fits:∀z,D (fun i=>(W i).tester S h z)=z)(i:Fin a)(N per:ℕ)(live:(W i).t≤N):
    FilteredWilsonProduct.listen (detector W D fits) i (N,per)=(calibrated S (W i)).plot N per:=by
  let e:=exterior S (W i)
  funext U
  let slots:=fun k:Fin e.length=>C.seen (detectorRaw S ((e.get k).2))
    (ceilSite C N per ((e.get k).1)) U
  change (∏k:Fin e.length, C.O N per (detectorRaw S ((e.get k).2)).2
    (ceilSite C N per ((e.get k).1))) U=_
  rw [Finset.prod_apply]
  change ∏k,slots k=∏j:Fin (W i).n,C.seen (detectorRaw S (S.classTokens ((W i).q j)))
    (location C.S (W i).t N per ((W i).x j)) U
  rw [←Equiv.prod_comp (index S (W i)) slots]
  apply Finset.prod_congr rfl
  intro j _
  dsimp only [slots,e]
  rw [entry]
  change C.seen _ (ceilSite C N per (C.S.gridPoint (W i).t ((W i).x j))) U=_
  rw [grid _ _ _ live]

end YM.Integration.WilsonMacroscopicRichWatchPlot
