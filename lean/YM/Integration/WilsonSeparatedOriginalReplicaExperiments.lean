import YM.Integration.WilsonSeparatedOriginalReplicaMeeting

/-! Exact seven-experiment evaluation of one whole signed physical profile at common finite positions. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonSeparatedOriginalReplicaExperiments
open Function Filter Finset MeasureTheory Lattice Wilson RG Source RG05Readout RG05Readout.Native
open RG05Readout.Pulse RG05Readout.Flatten RG05Readout.Nuclear RG05Readout.Address PhysicalNext.Repeat.Legato
open WilsonSeparatedOriginalPairedFolio
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){n N per u:ℕ}
variable (s:Fin 3→ℕ)(v:(i:Fin 3)→Palette R.family (s i))(h:n≤N)

def current (Ψ:Wave (Fin 3))(r:ℝ)(g:Body)(o:Fin 3→Site (R.family.side n per)):
    C(Fin 3 → Config G (R.family.side N per),ℂ):=⟨_,WilsonSeparatedOriginalReplicaRegularity.regular s v o h Ψ r g⟩

def assembled (Ψ:Wave (Fin 3))(r:ℝ)(g:Body)(m:ℕ):C(Fin 3 → Config G (R.family.side N per),ℂ):=
  premiums R.family s m n r • ∑o:Fin 3→Site (R.family.side n per),current R s v h Ψ r g o

theorem diagonal (Ψ:Wave (Fin 3))(r:ℝ)(g:Body)(m:ℕ)(U:Config G (R.family.side N per)):
    assembled R s v h Ψ r g m (fun _=>U)=constellation (C:=R.family) s v r Ψ h m g U:=by
  unfold assembled constellation
  simp only [ContinuousMap.smul_apply,ContinuousMap.sum_apply,Pi.smul_apply,Finset.sum_apply,smul_eq_mul]
  congr 1;apply sum_congr rfl;intro o _
  change (∫z in Native.box,g.val z*WilsonSeparatedOriginalReplicaWave.scalp s v o h (cropX Ψ o r z) (fun _=>U))=_
  unfold meet;apply integral_congr_ae;filter_upwards with z;rw [WilsonSeparatedOriginalReplicaRegularity.diagonal]

theorem counted (op:u+1≤N)(V:Config G (R.family.side u per))(o:Fin 3→Site (R.family.side n per))
    {r η X:ℝ}(rp:0<r)(room:r≤R.family.S.a n)(sep:0<η)(small:η≤1)
    (Ψ:Wave (Fin 3))(rank:ℕ)(grade:(∑i:Fin 3,(s i+2))+4*Fintype.card (Fin 3)<rank+1)
    (scatter:Scattering Ψ η)(xp:0≤X)(sizeX:Tall Ψ (rank+1) 1 X)(g:Body):
    WilsonSeparatedOriginalReplicaMeasure.read (WilsonMacroscopicRichFlatPosteriorLaw.law R N per op V)
      (current R s v h Ψ r g o)=∫z in Native.box,g.val z*WilsonSeparatedOriginalReplicaScanner.sample R s v o h op V (cropX Ψ o r z):=by
  obtain ⟨F,purse,cuts⟩:=regent s (C:=R.family) (p:=per) h o r η Ψ rp room sep small grade scatter xp sizeX
  let book:=fun (_:Fin 3→Body) (_:Unit→ℂ)=>True
  obtain ⟨L,hL,hF⟩:=WilsonSeparatedOriginalPairedFolio.issued (book:=book) purse (fun _ _=>⟨fun _=>0,True.intro⟩)
  apply WilsonSeparatedOriginalReplicaMeeting.original R s v o h op V Ψ r g L
  intro z hz;rw [hF hz];exact cuts z

theorem original (op:u+1≤N)(V:Config G (R.family.side u per))
    {r η X:ℝ}(rp:0<r)(room:r≤R.family.S.a n)(sep:0<η)(small:η≤1)
    (Ψ:Wave (Fin 3))(rank:ℕ)(grade:(∑i:Fin 3,(s i+2))+4*Fintype.card (Fin 3)<rank+1)
    (scatter:Scattering Ψ η)(xp:0≤X)(sizeX:Tall Ψ (rank+1) 1 X)(g:Body)(m:ℕ):
    WilsonSeparatedOriginalReplicaMeasure.read (WilsonMacroscopicRichFlatPosteriorLaw.law R N per op V)
      (assembled R s v h Ψ r g m)=premiums R.family s m n r*∑o:Fin 3→Site (R.family.side n per),
        ∫z in Native.box,g.val z*WilsonSeparatedOriginalReplicaScanner.sample R s v o h op V (cropX Ψ o r z):=by
  letI:=WilsonMacroscopicRichFlatPosteriorLaw.prob R op le_rfl V
  let μ:=WilsonMacroscopicRichFlatPosteriorLaw.law R N per op V
  change WilsonSeparatedOriginalReplicaMeasure.read μ (assembled R s v h Ψ r g m)=_
  rw [←WilsonSeparatedOriginalReplicaFunctional.measured,assembled,map_smul,map_sum,smul_eq_mul]
  congr 1;apply sum_congr rfl;intro o _
  rw [WilsonSeparatedOriginalReplicaFunctional.measured]
  exact counted R s v h op V o rp room sep small Ψ rank grade scatter xp sizeX g

end YM.Integration.WilsonSeparatedOriginalReplicaExperiments
