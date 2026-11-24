import YM.Integration.WilsonPositionProgramTrialBasedGhost
import YM.FVA2.FpWarm

/-! The orbit-link regulator and the based, even site FP space used by the
finite Fourier graph. The oriented orbit chart uses the head-minus-tail gauge
variation, so its based coordinate has the corresponding sign. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialSiteGauge
open Lattice Gauge FormalOPE.RG10 FormalOPE.RG10.BlockGauge
open PertExtension PertExtension.Series PertExtension.Orb PertExtension.Chart
open Function Finset FVA2 FVA2.Trans FVA2.Wilson Precision Inherit Push.Loops TreeBasis
open scoped Classical BigOperators
variable (G : Gauge) (n : Side)

def link (even : Even n.val) : Cone G n →ₗ[ℝ] ↥(Pert.Orb.LinkP G n) :=
  (coverL G n).codRestrict _ (fun x => cover_reflect G n even x)

def parameter : Param G n →ₗ[ℝ] ↥(Pert.Orb.Zero G n) where
  toFun p := ⟨fun x=>siteCover G n p 0-siteCover G n p x,
    ⟨fun x=>by dsimp only; rw [evenSite],by change siteCover G n p 0-siteCover G n p 0=0; exact sub_self _⟩⟩
  map_add' a b := by
    apply Subtype.ext
    funext x
    change siteCover G n (a+b) 0-siteCover G n (a+b) x=(_-_)+(_-_)
    simp only [map_add,Pi.add_apply]
    abel
  map_smul' r a := by
    apply Subtype.ext
    funext x
    change siteCover G n (r • a) 0-siteCover G n (r • a) x=r • (_-_)
    rw [map_smul,Pi.smul_apply,Pi.smul_apply,smul_sub]

theorem gradient (e : Even n.val) (p : Param G n) :
    link G n e (d G (rim n) p)=Pert.Orb.gZ (parameter G n p) := by
  apply Subtype.ext
  funext l
  change coverL G n (d G (rim n) p) l=(_-_)-(_-_)
  rw [differential]
  abel

theorem bijective (e : Even n.val) : Bijective (parameter G n) := by
  refine ⟨?_,?_⟩
  · intro p q h
    apply d_inj G (staple n)
    apply coverL_inj G n
    have eq := congrArg Subtype.val ((gradient G n e p).trans
      ((congrArg Pert.Orb.gZ h).trans (gradient G n e q).symm))
    exact eq
  · intro f
    let μ:=MS.Orbit.νt n • ∑ x, f.val x
    have fe : ∀x, f.val (-x)=f.val x := (show _ ∧ _ from f.property).1
    have even (x:Site n) : μ-f.val (-x)=μ-f.val x := by rw [fe]
    have zero : ∑ x, (μ-f.val x)=0 := by
      rw [sum_sub_distrib,sum_const,card_univ,← Nat.cast_smul_eq_nsmul ℝ]
      dsimp [μ]
      rw [smul_smul,ν_card,one_smul,sub_self]
    obtain ⟨p,hp⟩:=in_sector G n even zero
    refine ⟨p,Subtype.ext (funext fun x => ?_)⟩
    change siteCover G n p 0-siteCover G n p x=f.val x
    rw [hp]
    dsimp only
    rw [Pert.Orb.atZ,sub_zero,sub_sub_cancel]

def reporter (e : Even n.val) : Cone G n →ₗ[ℝ] ↥(Pert.Orb.Mean G n) :=
  Pert.Orb.dLin.comp (link G n e)

theorem original (e : Even n.val) :
    Bijective (reporter G n e ∘ₗ d G (rim n)) := by
  have fields : reporter G n e ∘ₗ d G (rim n) = Pert.Orb.bridge G n ∘ₗ parameter G n := by
    apply LinearMap.ext
    intro p
    change Pert.Orb.dLin (link G n e (d G (rim n) p))=_
    rw [gradient]
    rfl
  rw [fields]
  exact ((Pert.Orb.bridgeEquiv G n).bijective.comp (bijective G n e))

end YM.Integration.WilsonPositionProgramTrialSiteGauge
