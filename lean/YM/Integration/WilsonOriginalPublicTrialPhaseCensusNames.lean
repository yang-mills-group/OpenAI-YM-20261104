import YM.Integration.WilsonOriginalPublicTrialPhaseFaceCenter
import YM.Contacts.Fusion.Relabel

/-! Removing the single auxiliary tile label preserves the entire screened Wilson programme. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicTrialPhaseCensusNames
open Finset Function MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof MergeProof.Accent MergeProof.Menu Marker Ac
open GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat PhysicalNext.Repeat.Lotus
open RG05Readout RG05Readout.Address RG05Readout.Many RG05Readout.Pantry
open OPE.Therm Push.GridApprox PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Campaign
open Cells WilsonOriginalPublicTrialPhaseCenterMenu
open scoped Classical BigOperators ContDiff
open WilsonOriginalPublicTrialPhaseTiles
open MergeProof.Bouquet
open WilsonOriginalPublicTrialPhaseFaceCenter
variable {G:Gauge}{V W:Type}[Fintype V][DecidableEq V][Fintype W][DecidableEq W]

def unmark (V:Type):Unit×V≃V where
  toFun:=Prod.snd
  invFun:=fun v=>((),v)
  left_inv:=fun ⟨⟨⟩,_⟩=>rfl
  right_inv:=fun _=>rfl

theorem relabel (e:V≃W)(A:History G)(N per K:ℕ){u:ℕ}(uk:u≤K)
    (F:Config G (A.S.side K per)→Poly (Stock.census V))(hF:Integrable F (prior G _)):
    (Relabel.walk e) ∘ gust A N per K F u uk=gust A N per K (Relabel.walk e ∘ F) u uk:=by
  have rest:Integrable (Relabel.walk e ∘ F) (prior G _):=((Relabel.walk e).restrictScalars ℝ).integrable_comp hF
  funext U
  ext p
  obtain ⟨q,rfl⟩:=(Relabel.mode e).surjective p
  rw [Function.comp_apply,Relabel.part,congrFun (slice A N per K F hF uk q) U,
    congrFun (slice A N per K (Relabel.walk e ∘ F) rest uk (Relabel.mode e q)) U]
  have same:(fun W=>((Relabel.walk e ∘ F) W).part (Relabel.mode e q))=(fun W=>(F W).part q):=
    funext fun W=>Relabel.part e (F W) q
  rw [same]

variable (R:Run G){j u K per N:ℕ}
local notation "C" => R.family
local notation "P" => (C).path.rep N per
local notation "T" => Site ((C).side j per)

theorem unpadded (jk:j≤K)(M:Config G ((C).side K per)→ℂ):
    Relabel.walk (unmark (T)) ∘ cohort R (N:=N) jk M=WilsonOriginalPublicTrialPhaseTerminal.opening R (N:=N) jk M:=by
  funext U
  unfold cohort WilsonOriginalPublicTrialPhaseTerminal.opening birth
  rw [Function.comp_apply,map_smul,Relabel.pass,Relabel.mach]
  rfl

theorem funds (jk:j≤K)(live:K≤N)(M:Config G ((C).side K per)→ℂ)(regular:Continuous M):
    Integrable (cohort R (N:=N) jk M) (prior G _) ∧
    Integrable (fun U=>(((P) K).eval U:ℂ)*M U) (prior G _):=by
  let t:=tilesAt (C).S per jk
  have hcopy(v:Unit×(T)):Continuous (t.copy v.2 M):=by
    have h:=regular.comp (continuous_pull (G:=G) (t.omega v.2) (t.translateBy v.2))
    unfold Tiling.copy
    split <;> first | exact h.star | exact h
  have ht:=RG02.Actual.eval_cont R.makes.wilson live (p:=per)
  let core : Config G ((C).side K per)→ℂ := fun U=>(((P) K).eval U:ℂ)*M U
  have core_cont:Continuous core :=(Complex.continuous_ofReal.comp ht).mul regular
  have paid_core:Integrable core (prior G ((C).side K per)):=
    core_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  exact ⟨(hatCont (C) K per _ hcopy ht (Stock.census (Unit×(T)))).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _),
    paid_core⟩

theorem submitted (ju:j≤u)(uk:u≤K)(live:K≤N)(M:Config G ((C).side K per)→ℂ)(regular:Continuous M):
    Relabel.walk (unmark (T)) ∘ gust (C).path N per K (cohort R (N:=N) (ju.trans uk) M) u uk=
      WilsonOriginalPublicTrialPhaseTerminal.arrival R (N:=N) (ju.trans uk) uk M:=by
  rw [relabel _ _ _ _ _ uk _ (funds R (ju.trans uk) live M regular).1,unpadded]
  rfl

end YM.Integration.WilsonOriginalPublicTrialPhaseCensusNames
end
