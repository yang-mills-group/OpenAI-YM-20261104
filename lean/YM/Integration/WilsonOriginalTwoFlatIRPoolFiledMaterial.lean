import YM.Integration.WilsonOriginalTwoFlatIRPoolOriginalCommission
import YM.Integration.WilsonReceivedChronologicalFixedRoseGridPostedProgramme
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatIRPoolFiledMaterial
open Function Filter Finset Lattice Laurent Wilson RG Source Labels
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Realm
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider
open WilsonThermometerDeclaredSeeds WilsonOriginalMixedBlockRows
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Extra.Histories Extra.Trajectories Extra.Multi
open RG16.Literal OPE Overlay Bid Push.GridApprox
open PertExtension Series WilsonCoeffUV.Bank.Mosaic.Near
open WilsonOriginalObservedRoseVanePurse (ages)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonReceivedChronologicalFixedRoseFittedDebit (Plan)
open WilsonReceivedCanonicalSocketSeed (contact)
open scoped Classical BigOperators
variable {G:Gauge}
open WilsonOriginalTwoFlatIRPoolFiledClosure (Closed)
open WilsonOriginalTwoFlatIRPoolOriginalCommission (OnFile)
open WilsonMovingForkStencilCatalogue (Catalogue table)
open WilsonMovingForkStencilProgramme (Basis coefficient)
open WilsonReceivedChronologicalFixedRoseGridPostedProgramme (declaration)

def Assembled (R:Run G){K:ℕ}(source:Catalogue R ages K)(file:Filed R ages K):Prop:=
  (∀N per:ℕ,∀w:∀i,R.family.label (ages i),∀ξ:Fin 3→Site (R.family.side K per),K ≤ N →
    file.row N per w ξ K=WilsonMovingForkMixedSeed.product R ages (N:=N) ξ w) ∧
  ∀N per:ℕ,∀w:∀i,R.family.label (ages i),∀ξ:Fin 3→Site (R.family.side K per),
  ∀j:ℕ,∀live:j < K,∀U:Config G (R.family.side j per),
    file.row N per w ξ j U=∑b:Basis R ages,coefficient (R:=R) (d:=ages) (K:=K) N per w b*
      (let H:=declaration R ages source b N per w ξ j live
       (WilsonOriginalTwoFlatIRMounted.value H.binder H.load H.copies (Pert.Asymptotics.regulatorRun R.family N per j)
         H.wallet U).part (WilsonMovingForkPrintedFile.allSlots 3))

/-- On the enrolled independent catalogue, print the full finite sum with the actual measured
coordinates. Its complete upper product and lower ordinary rows retain the original fiscal reading. -/
theorem original (R:Run G)(l:Filter (ℕ×ℕ))(D:Fin 3→ℕ)(pt:Fin 3→Chamber)(φ:Test 3)
    (dates:Fin 3→ℕ)(labels:∀i:Fin 3,ℕ×ℕ→R.family.label (ages i))(M:Fin 3→ℝ)
    (r γ:ℝ)(sensor:ℂ)(margin:ℝ){u f K:ℕ}(uf:u ≤ f)(fk:f ≤ K)(c m Q J₀ requested tag target src apron:ℕ)
    (plan:Plan 3){top:ℕ}{Vc:Realm G (top+1) Credit.leanC}(drawc:Vc.draws=R.family.path.levels)
    (source:Catalogue R ages K)(sale:OnFile R l D pt φ dates labels M r γ sensor margin uf fk
      c m Q J₀ requested tag target src apron plan drawc):
    ∃file:Filed R ages K,(∀i,file.station i=dates i) ∧ file.target=target ∧ Assembled R source file ∧
      Closed R l D pt φ dates labels M r γ sensor margin uf fk c m Q J₀ requested tag src apron plan file drawc:=by
  classical
  let first:Basis R ages:=fun _=>.inl ()
  obtain ⟨old,stations,grade,_,paid⟩:=sale (declaration R ages source first)
  let actual:=WilsonMovingForkStencilProgramme.issued (table source) (fun i=>contact (D i)) pt old
  refine ⟨actual,stations,grade,⟨?_,?_⟩,paid⟩
  · intro N per w ξ live
    exact WilsonMovingForkStencilProgramme.cutoff (table source) (fun i=>contact (D i)) pt N per w ξ live
  · intro N per w ξ j live U
    simp only [actual,WilsonMovingForkStencilProgramme.issued,WilsonMovingForkStencilProgramme.row,
      WilsonMovingForkStencilProgramme.piece,live,↓reduceDIte,declaration]
    rfl

end YM.Integration.WilsonOriginalTwoFlatIRPoolFiledMaterial
