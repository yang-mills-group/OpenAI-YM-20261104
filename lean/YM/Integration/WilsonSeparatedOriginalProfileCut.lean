import YM.Integration.WilsonAllDateHarvestNuclearProgram
import YM.Integration.WilsonSeparatedOriginalProfileCensus
import YM.Integration.WilsonPositionSeparatedProfileCenteredMeasured

/-! A filed smeared cubic on the genuine primary Wilson fields at a fixed earlier observation. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonSeparatedOriginalProfileCut
open Function Filter Finset MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Push Local Marker
open RG05Readout RG05Readout.Many RG05Readout.Native RG05Readout.Pulse RG05Readout.Flatten RG05Readout.Nuclear
open RG05Readout.Address RG05Readout.View PhysicalNext.Repeat.Legato WilsonCloseCaptureCalendar
open Extraction Spec RG12 RG17 WilsonSeparatedOriginalProfilePortfolio WilsonSeparatedOriginalPairedFolio
open WilsonAllDateHarvestFiledReplay WilsonAllDateHarvestNuclearProgram
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G)(portfolio:Funding R)
  {order:Extraction.Order}{table:Table R.family.book}{F:Final R.family order table}(L:Layout F)
variable {n m t N per d H k:ℕ}

def masks:Census (Fin 3) where
  choices:=univ
  blank:=mem_univ _
  solo _:=mem_univ _
  down _ _ _:=mem_univ _

theorem full:univ∈masks.choices:=mem_univ _

def physical (s:Fin 3→ℕ)(w:(i:Fin 3)→R.family.label (s i))(r:ℝ)(Ψ:Wave (Fin 3))(g:Body)
    (j:ℕ)(nN:n<N)(V:Config G (R.family.side n per)):ℂ:=
  WilsonSeparatedOriginalReplicaMeasure.read (WilsonMacroscopicRichFlatPosteriorLaw.law R N per nN V)
    (WilsonSeparatedOriginalReplicaExperiments.assembled R s
      (WilsonPositionSeparatedProfileCenteredMeasured.upper R L s w r N per) nN.le Ψ r g j)

def Settled (s:Fin 3→ℕ)(w:(i:Fin 3)→R.family.label (s i))(Ψ:Wave (Fin 3))(g:Body)
    (rank:ℕ)(r η X cap fee target:ℝ)(_nm:n ≤ m)(_mt:m ≤ t)(nt:n < t)(tN:t ≤ N)
    (P:(v:Fin 3)→Sight R.family (s v) per):Prop:=
  let S:=fun v:Fin 3=>portfolio.basis (s v) (N,per)
  let x:=fun v:Fin 3=>WilsonReportHarvestReadmittedSource.filed L (s v) r (w v) (S v) m N per
  let y:=WilsonAllDateHarvestRebook.raised s S x m t
  let A:=Pulse.area (C:=R.family) (p:=per) (b:=n) (V:=Fin 3) ⌈cap+2⌉₊
  let admit:=fun o=>allowed R o s S y P masks full nt tN r η fee
  let sale:=fun o=>WilsonSeparatedOriginalProfileColumn.Posted R o s S y P masks full nt tN fee
  ∃T:(o:Fin 3→Site (R.family.side n per))→List (Entry s (admit o) (sale o)),
    (∀o,o∉A → T o=[]) ∧ (∀o∈A,((T o).map Entry.rent).sum ≤ earn s R.family n rank η r*X) ∧
    ∀(j:ℕ)(V:Config G (R.family.side n per)),flags (R.family.path.rep N per n).p.threshold V=∅ →
      ‖physical R L s w r Ψ g j (nt.trans_le tN) V-
        premiums R.family s j n r*∑o:Fin 3→Site (R.family.side n per),received g (T o) V‖ ≤ target

theorem purchased (s:Fin 3→ℕ)(w:(i:Fin 3)→R.family.label (s i))(Ψ:Wave (Fin 3))(g:Body)
    (rank:ℕ){r η X cap fee target:ℝ}(nm:n ≤ m)(mt:m ≤ t)(nt:n < t)(tN:t ≤ N)
    (P:(v:Fin 3)→Sight R.family (s v) per)(ep:0 ≤ fee)(rp:0<r)(room:r ≤ R.family.S.a n)
    (sep:0<η)(small:η ≤ 1)(grade:(∑i:Fin 3,(s i+2))+4*Fintype.card (Fin 3)<rank+1)
    (scatter:Scattering Ψ η)(xp:0 ≤ X)(sizeX:Tall Ψ (rank+1) 1 X)
    (cp:0 ≤ cap)(shape:∀z∈tsupport Ψ.val,∀i:Fin 3,‖z i‖ ≤ cap)
    (margin:2*(R.family.S.a n*(2*(⌈cap+2⌉₊:ℝ)+1))<R.family.S.radius per)
    (filed:Registered R portfolio L s r w n m N per d H P)
    (cash:Purchases R portfolio L s r η w nm mt tN per d H k P fee)
    (price:WilsonSeparatedOriginalProfileTariff.budget R.family s n rank r η X cap g*fee ≤ target):
    Settled R portfolio L s w Ψ g rank r η X cap fee target nm mt nt tN P:=by
  let S:=fun v:Fin 3=>portfolio.basis (s v) (N,per)
  let x:=fun v:Fin 3=>WilsonReportHarvestReadmittedSource.filed L (s v) r (w v) (S v) m N per
  let y:=WilsonAllDateHarvestRebook.raised s S x m t
  have actual:(fun i=>Launch (m:=t) s S y i N)=WilsonPositionSeparatedProfileCenteredMeasured.upper R L s w r N per:=by
    funext i
    exact (congrFun (congrFun (WilsonAllDateHarvestRebook.launch s S x m t) i) N).trans (filed.2 i).2
  obtain ⟨T,zero,rents,bound⟩:=WilsonSeparatedOriginalProfileCensus.original R s S y (fun _=>P) (fun _=>masks)
    (fun _=>full) nt tN (d+1) k (WilsonReportHarvestReplayPhysical.allowance R m N d H*(R.family.S.a m/R.family.S.a t)) fee ep
    rp room sep small Ψ rank grade scatter xp sizeX cp shape (fun o ho=>cash _ o ho margin masks)
  refine ⟨T,zero,rents,?_⟩;intro j V healthy
  have result:WilsonSeparatedOriginalProfileCensus.collected R s S y nt tN Ψ r j g V=physical R L s w r Ψ g j (nt.trans_le tN) V:=by
    unfold WilsonSeparatedOriginalProfileCensus.collected physical;rw [actual]
  rw [←result];exact (bound j g V healthy).trans price

end YM.Integration.WilsonSeparatedOriginalProfileCut
