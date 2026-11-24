import YM.Integration.WilsonOriginalPublicTrialPhaseCensusNames
import YM.Integration.WilsonOriginalPublicTrialPhaseGroup

/-! The paid grouping at capture takes the exact product of the constituent K stencil words on every tile. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicTrialPhaseGroupedWord
open Finset Function MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof MergeProof.Accent MergeProof.Menu Marker Ac
open GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat PhysicalNext.Repeat.Lotus
open RG05Readout RG05Readout.Address RG05Readout.Many RG05Readout.Pantry
open OPE.Therm Push.GridApprox PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Campaign
open Cells WilsonOriginalPublicTrialPhaseCenterMenu
open scoped Classical BigOperators ContDiff
open WilsonOriginalPublicTrialPhaseTiles
open WilsonPositionProgramBlockedTrialAddBack
open WilsonOriginalPublicTrialPhaseGroup WilsonOriginalPublicTrialPhaseFaceCenter
variable {G:Gauge}{V I:Type}[Fintype V][DecidableEq V][Fintype I][DecidableEq I]

theorem grouped (i:I)(s:(Stock.census (Unit×V)).Mode)(g:V×I→ℂ):
    ∏ j∈(contents i s).val,g j=∏ v∈s.val,∏ k:I,g (v.2,k):=by
  have inj:Set.InjOn Prod.snd (s.val:Set (Unit×V)):=fun _ _ _ _ he=>Prod.ext (Subsingleton.elim ..) he
  have roster:(contents i s).val=(s.val.image Prod.snd) ×ˢ (univ:Finset I):=by
    ext j
    rw [inside,mem_product,mem_image]
    simp only [mem_univ,and_true]
    exact ⟨fun hj=>⟨((),j.1),hj,rfl⟩,fun ⟨⟨⟨⟩,v⟩,hv,eq⟩=>eq ▸ hv⟩
  rw [roster,prod_product,prod_image inj]

theorem pool {n:Side}(Q:Rep G n)(a:I)(M:V×I→ Config G n→ℂ):
    (fun U=>collect a (birth (Stock.census (V×I)) Q M U))=
      birth (Stock.census (Unit×V)) Q (fun j U=>∏i:I,M (j.2,i) U):=by
  funext U
  ext s
  rw [WilsonOriginalPublicTrialPhaseGroup.part]
  unfold birth Mach
  rw [Poly.part_smul,Poly.part_smul,pass_fire,pass_fire,grouped]

variable (R:Run G){j m K per N:ℕ}
local notation "C" => R.family
local notation "P" => (C).path.rep N per
local notation "T" => Site ((C).side j per)
def origin (jk:j≤K)(d:I→ℕ)(z:I→Site ((C).side K per))(v:∀i,(C).label (d i)):
    Config G ((C).side K per)→Poly (Stock.census ((T)×I)):=
  birth (Stock.census ((T)×I)) ((P) K) (fun k=>(tilesAt (C).S per jk).copy k.1
    (uncut R (d k.2) N per K (z k.2) (v k.2)))

theorem birth_word (jk:j≤K)(d:I→ℕ)(z:I→Site ((C).side K per))(v:∀i,(C).label (d i))(k:I):
    (fun U=>collect k (origin R (N:=N) jk d z v U))=
      cohort R (N:=N) jk (WilsonOriginalPublicTrialPhaseTrace.word R (N:=N) d z v):=by
  unfold origin cohort
  rw [pool]
  apply congrArg (birth _ _)
  funext a U
  let t:=tilesAt (C).S per jk
  by_cases hand:t.hand a.2
  · simp [WilsonOriginalPublicTrialPhaseTrace.word,Tiling.copy,show (tilesAt (C).S per jk).hand a.2 from hand]
  · simp [WilsonOriginalPublicTrialPhaseTrace.word,Tiling.copy,show ¬(tilesAt (C).S per jk).hand a.2 from hand]

theorem original (jk:j≤K)(mk:m≤K)(live:K≤N)(d:I→ℕ)(z:I→Site ((C).side K per))
    (v:∀i,(C).label (d i))(k:I):
    (fun U=>collect k (gust (C).path N per K (origin R (N:=N) jk d z v) m mk U))=
      gust (C).path N per K (cohort R (N:=N) jk (WilsonOriginalPublicTrialPhaseTrace.word R (N:=N) d z v)) m mk:=by
  let Q:=origin R (N:=N) jk d z v
  let A:=cohort R (N:=N) jk (WilsonOriginalPublicTrialPhaseTrace.word R (N:=N) d z v)
  have earned:Integrable Q (prior G _):=by
    let t:=tilesAt (C).S per jk
    have hc(k:(T)×I):Continuous (t.copy k.1 (uncut R (d k.2) N per K (z k.2) (v k.2))):=by
      have f:Continuous (uncut R (d k.2) N per K (z k.2) (v k.2)):=by
        unfold uncut;exact continuous_const.add (((C).localSection _).continuous_places _ _)
      have h:=f.comp (continuous_pull (G:=G) (t.omega k.1) (t.translateBy k.1))
      unfold Tiling.copy;split <;> first | exact h.star | exact h
    exact (hatCont (C) K per _ hc (RG02.Actual.eval_cont R.makes.wilson live) _).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have spent:Integrable A (prior G _):=(WilsonOriginalPublicTrialPhaseCensusNames.funds R (N:=N) jk live
    (WilsonOriginalPublicTrialPhaseTrace.word R (N:=N) d z v) (WilsonOriginalPublicTrialPhaseWhole.continuous_file R (N:=N) d z v)).1
  have joined:=birth_word R (N:=N) jk d z v k
  funext U
  ext s
  rw [WilsonOriginalPublicTrialPhaseGroup.part,congrFun (slice (C).path N per K Q earned mk (contents k s)) U,
    congrFun (slice (C).path N per K A spent mk s) U]
  have head:(fun U=>(Q U).part (contents k s))=(fun U=>(A U).part s):=by
    funext U
    simpa only [WilsonOriginalPublicTrialPhaseGroup.part] using congrArg (fun p=>p.part s) (congrFun joined U)
  rw [head]

end YM.Integration.WilsonOriginalPublicTrialPhaseGroupedWord
end
