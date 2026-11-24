import YM.Integration.WilsonSeparatedOriginalReplicaExperiments
import YM.Integration.WilsonSeparatedOriginalProfileTariff

/-! The complete original connected clamped experiment and its filed lower roster under one cutoff-independent price. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonSeparatedOriginalProfileCensus
open Function Filter Finset MeasureTheory Lattice Wilson RG Source Extra.Histories Push Local Marker
open RG05Readout RG05Readout.Many RG05Readout.Native RG05Readout.Pulse RG05Readout.Flatten RG05Readout.Nuclear
open RG05Readout.Address RG05Readout.View PhysicalNext.Repeat.Legato WilsonAllDateHarvestObservedReplay
open WilsonSeparatedOriginalProfilePortfolio WilsonSeparatedOriginalPairedFolio
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){n t N per:ℕ}
variable (s:Fin 3→ℕ)(S:(i:Fin 3)→Emblems R.family (s i))(x:(i:Fin 3)→Palette R.family (s i))
variable (P:(Fin 3→Site (R.family.side n per))→(i:Fin 3)→Sight R.family (s i) per)(roster:(Fin 3→Site (R.family.side n per))→Census (Fin 3))
    (full:∀o,univ∈(roster o).choices)(nt:n<t)(tN:t≤N)

def collected (Ψ:Wave (Fin 3))(r:ℝ)(m:ℕ)(g:Body)(V:Config G (R.family.side n per)):ℂ:=
  WilsonSeparatedOriginalReplicaMeasure.read (WilsonMacroscopicRichFlatPosteriorLaw.law R N per (nt.trans_le tN) V)
    (WilsonSeparatedOriginalReplicaExperiments.assembled R s (fun i=>Launch (m:=t) s S x i N) (nt.le.trans tN) Ψ r g m)

theorem original (d k:ℕ)(Q fee:ℝ)(ep:0≤fee)
    {r η X cap:ℝ}(rp:0<r)(room:r≤R.family.S.a n)(sep:0<η)(small:η≤1)
    (Ψ:Wave (Fin 3))(rank:ℕ)(grade:(∑i:Fin 3,(s i+2))+4*Fintype.card (Fin 3)<rank+1)
    (scatter:Scattering Ψ η)(xp:0≤X)(sizeX:Tall Ψ (rank+1) 1 X)
    (cp:0≤cap)(shape:∀y∈tsupport Ψ.val,∀i:Fin 3,‖y i‖≤cap)
    (buying:∀o∈Pulse.area (C:=R.family) (p:=per) (b:=n) ⌈cap+2⌉₊,
      ∀f:Fin 3→Body,(∀i,Tall (f i) (s i+2) 1 1) → buy R.family n per o (r*η/2) f →
      Captured o (fun _=>(1,false)) s (fun z=>f z.val.1) R.makes (P o) S x (roster o) nt.le tN d k Q fee):
    let admit:=fun o=>allowed R o s S x (P o) (roster o) (full o) nt tN r η fee
    let sale:=fun o=>WilsonSeparatedOriginalProfileColumn.Posted R o s S x (P o) (roster o) (full o) nt tN fee
    let A:=Pulse.area (C:=R.family) (p:=per) (b:=n) (V:=Fin 3) ⌈cap+2⌉₊
    ∃L:(o:Fin 3→Site (R.family.side n per))→List (Entry s (admit o) (sale o)),(∀o,o∉A → L o=[]) ∧
      (∀o∈A,((L o).map Entry.rent).sum≤earn s R.family n rank η r*X) ∧
      ∀(m:ℕ)(g:Body)(V:Config G (R.family.side n per)),flags (R.family.path.rep N per n).p.threshold V=∅ →
        ‖collected R s S x nt tN Ψ r m g V-premiums R.family s m n r*∑o:Fin 3→Site (R.family.side n per),received g (L o) V‖≤
          WilsonSeparatedOriginalProfileTariff.budget R.family s n rank r η X cap g*fee:=by
  obtain ⟨L,empty,cost,paid⟩:=WilsonSeparatedOriginalProfileParents.original R s S x P roster full nt tN d k Q fee ep rp room sep small Ψ rank grade scatter xp sizeX cp shape buying
  refine ⟨L,empty,cost,?_⟩;intro m g V healthy
  have same:collected R s S x nt tN Ψ r m g V=WilsonSeparatedOriginalProfileParents.whole R s S x nt tN r Ψ m g V:=
    WilsonSeparatedOriginalReplicaExperiments.original R s (fun i=>Launch (m:=t) s S x i N) (nt.le.trans tN) (nt.trans_le tN) V rp room sep small Ψ rank grade scatter xp sizeX g m
  rw [same];exact (paid m g V healthy).trans (WilsonSeparatedOriginalProfileTariff.full R.family s m n rank rp η X cap g ep)

end YM.Integration.WilsonSeparatedOriginalProfileCensus
