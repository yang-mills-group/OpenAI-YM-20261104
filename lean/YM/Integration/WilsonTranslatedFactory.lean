import YM.Integration.WilsonTranslatedSourceBudget
import YM.Source.Construction
import YM.Extra.SOURCE_HISTORIES.Motion
import YM.Push.GRID_APPROXIMATION.Bounds

/-! The actual calibrated Wilson insertion on any site of every retained
regulator. The unnormalized step below reaches the embedded fine site. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonTranslatedFactory
open Function Lattice RG Wilson Source Push.Local Extra.Histories
open scoped Classical
variable {G : Gauge} {C : Family G} (h : C.Makes) {N p d m : ℕ}

private def motion (hm : m ≤ N) (y : Site (C.side m p)) :=
  ((h.wilson.represents N p m hm).good.labels.moves (1 : Signed) y).some

def entry (hm : m ≤ N) (y : Site (C.side m p)) (v : C.label d) :=
  reorient (motion h hm y) ((C.factory d N p).entries m v)

theorem coordinate (hm : m ≤ N) (y : Site (C.side m p)) (v : C.label d) :
    (entry h hm y v).x = ((C.factory d N p).entries m v).x := by
  simp only [entry,reorient,show (1:Signed).ortho=1 from map_one Signed.inclusionO,Labels.Frame.act_one]

theorem based (hrs : C.ref d ≤ m) (hm : m ≤ N) (y : Site (C.side m p)) (v : C.label d) :
    (entry h hm y v).Format y C.params (C.path.rep N p m) ∧
    (entry h hm y v).remBound y (C.path.rep N p m) (Real.sqrt (C.path.levels.clock.forcedAllowance m))
      ((C.path.levels.params m).columns * (C.labels.level d).coeffSize ((C.labels.level d).core (entry h hm y v).x)) := by
  have hc := h.calibrated d N p (hrs.trans hm)
  have size := h.places d m p hrs 0 (h.sections d).anchored 0
  have hn : 2 ≤ (C.side m p).val := by omega
  have ht := format_reorient (motion h hm y) (hc.format m hrs hm v) hn
  have he := WilsonTranslatedSourceBudget.translated y (motion h hm y) (hc.cap m hrs hm v)
  rw [coordinate]; exact ⟨by simpa only [entry,affine,Signed.act_zero,zero_add] using ht,
    by simpa only [entry,zero_add] using he⟩

theorem density (hm : m ≤ N) (y : Site (C.side m p)) (v : C.label d) :
    (entry h hm y v).density y (C.localSection d) (C.path.rep N p m) =
      ((C.factory d N p).entries m v).density 0 (C.localSection d) (C.path.rep N p m) ∘ pull 1 y := by
  simpa only [entry,affine,Signed.act_zero,zero_add] using
    density_reorient (o:=0) (motion h hm y) (h.sections d) ((C.factory d N p).entries m v)

theorem born (hr : C.ref d ≤ N) (y : Site (C.side N p)) (v : C.label d)
    (U : Config G (C.side N p)) :
    (entry h (le_refl N) y v).density y (C.localSection d) (C.path.rep N p N) U =
      ((C.S.a N : ℂ)^d) * ((C.path.rep N p N).eval U : ℂ) *
        initial (C.localSection d) C.path N p v y U := by
  rw [density,Function.comp_apply,(h.calibrated d N p hr).encode,eval_pull (motion h (le_refl N) y)]
  simp only [initial,Pi.smul_apply,pull_one,SectionData.places_trans,zero_add]

theorem transfer (hr : C.ref d ≤ m) (hm : m < N) (y : Site (C.side m p)) (v : C.label d) :
    (entry h hm.le y v).density y (C.localSection d) (C.path.rep N p m) =
      ((C.S.block m).val : ℂ)^d • (C.path.levels.clock.op m p).push (C.path.β N p (m+1))
        ((entry h hm ((C.path.levels.clock.op m p).ratio.embed y) v).density
          ((C.path.levels.clock.op m p).ratio.embed y) (C.localSection d) (C.path.rep N p (m+1))) := by
  have hc := h.calibrated d N p (hr.trans hm.le)
  have hi : MeasureTheory.Integrable (((C.factory d N p).entries (m+1) v).density 0
      (C.localSection d) (C.path.rep N p (m+1))) (prior G (C.side (m+1) p)) :=
    (((C.factory d N p).entries (m+1) v).envelope (C.localSection d)
    (h.wilson.represents N p (m+1) hm).good (hc.cap _ (by omega) hm v)
    (hc.format _ (by omega) hm v)).integrableC _
  rw [density,density,hc.unnormalized m hr hm v]; funext U
  exact congr_arg (fun z : ℂ => ((C.S.block m).val : ℂ)^d • z)
    (Motion.push_pull C.path m p (C.path.β N p (m+1)) 1 y _ hi U).symm

end YM.Integration.WilsonTranslatedFactory
