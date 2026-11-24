import YM.Integration.WilsonPositionProgramTrialPublicJointSourceProjected
/-! One actually purchased finite position inverse in each grade, shared by all
source coefficients, placements, tests, and proper faces of the experiment. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace YM.Integration.WilsonPositionProgramTrialPublicJointSourcePosition
open Filter Function Finset PowerSeries Maxwell RG Lattice Wilson Tree Source Labels XSpace XSpace.Cirrus XSpace.Normalize XSpace.Structure1 XSpace.Rose
open WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Blue WilsonCoeffUV.Cosmos WilsonCoeffUV.Embroider
open PhysicalNext.Repeat.Legato
open WilsonOriginalPublicNodalBufferedCellRow (Source)
open WilsonOriginalPublicNodalBufferedCellFilm (Disp)
open WilsonPositionProgramTrialPublicJointFirstSource (site)
open WilsonPositionProgramTrialPublicJointSourceProjected (input datum average positioned)
open WilsonPositionProgramTrialPublicJointPositionInlet (applyTo)
open scoped Classical BigOperators Topology
variable {G:Gauge}{n:ℕ}(R:Run G)(W:Initialize G)(V:Store G)(d D:Fin (n+1)→ℕ)(cut:∀i,d i<D i)

theorem original:∀ᶠ M:Mesh in Front,
    ∃U:(i:Fin (n+1))→Guard G (d i),
      (∀i,let Z:=deck (V.layout W M (d i));V.Meets W M (d i) ∧ Formal (U i) ∧ Z*U i=1 ∧ U i*Z=1 ∧
        ∀q,applyTo (U i) (fun j=>if j=0 then leaf G (d i) else 0) q=if q=0 then leaf G (d i) else 0) ∧
      ∀(grid:pack 2)(center:Four ℝ)(T:(i:Fin (n+1))→Rarity (D i))(x:Fin (n+1)→ℝ)(y σ:ℝ)
        (sp:0<σ)(o:Fin (n+1)→CellR)(m K:ℕ)(b:Source R d)(ξ:Disp n)(z:Fin (n+1)→Lattice.Cover)(i:Fin (n+1)),
        let Y:Sample 2:=⟨M,grid,center⟩
        let c:=input R W d D cut m K b
        let Gp:=average R W d D cut Y T x y σ sp o c ξ z i (positioned R W d Y z i K)
        let p:=datum R W d D cut Y T x y σ sp o m K b ξ z i
        let e:=applyTo (U i) p
        let Z:=deck (V.layout W M (d i))
        (∀j,∑l∈range (j+1),coeff l Z (e (j-l))=p j) ∧ ∀q,coeff q Gp=
          ∑t∈HasAntidiagonal.antidiagonal q,coeff t.2 (regal W (d i) (site Y z) (chartV (site Y z) i)
            (∑l∈range (t.1+1),coeff l Z (e (t.1-l)))):=by
  filter_upwards [eventually_all.mpr fun i=>WilsonPositionProgramTrialPublicJointPositionInlet.purchased W V (d i)] with M issued
  choose U rest using fun i=>(issued i).2
  refine ⟨U,fun i=>⟨(issued i).1,(rest i).1,(rest i).2.1,(rest i).2.2.1,(rest i).2.2.2.1⟩,?_⟩
  intro grid center T x y σ sp o m K b ξ z i Y c Gp p e Z
  have returned (j:ℕ):∑l∈range (j+1),coeff l Z (e (j-l))=p j:=(rest i).2.2.2.2 p j
  refine ⟨returned,fun q=>?_⟩
  simp_rw [returned]
  exact WilsonPositionProgramTrialPublicJointSourceProjected.coefficient R W d D cut Y T x y σ sp o m K b ξ z i q

end YM.Integration.WilsonPositionProgramTrialPublicJointSourcePosition
