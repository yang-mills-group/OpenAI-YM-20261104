import YM.Integration.WilsonIndependentMatchedTopFilm

/-! Evaluate the joint top before dividing by its one common vacuum.
All thermal coefficients of both true section stencils may vary independently. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedTopPair
open Finset Lattice RG RG.Supply Wilson Source Labels PhysicalNext.Repeat.Legato XSpace XSpace.Rose XSpace.Cirrus
open WilsonCoeffUV WilsonCoeffUV.Cosmos WilsonCoeffUV.Blue WilsonCoeffUV.Embroider
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Shard WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Bank WilsonCoeffUV.Power PowerSeries PertExtension FVA2 FormalOPE.RG10 FormalOPE.RG10.BlockGauge
open WilsonIndependentMatchedNamedPair (placed admitted)
open WilsonIndependentMatchedTopFilm (dose word)
open scoped Classical BigOperators
variable {G:Gauge}

private theorem row {p:Period}(W:Initialize G){F:Fabric G p.side}(cloth:F.Cloth)
    (z:F.Accounts→PowerSeries ℝ)(hz:∀a,0<coeff 0 (z a))(unit:z none=1)
    (f g:Config G p.side→ℝ)(hf:Orb.PreTest f)(hg:Orb.PreTest g)(c c':PowerSeries ℂ) :
    let T:=W.tree p
    Bare.normalized T G ((Bare.scalar T c*BareOrb.stencil T f)*(Bare.scalar T c'*BareOrb.stencil T g)) =
      (c*c')*TaylorWick.into (WilsonIndependentGroupedOrbit.paid cloth z hz (f*g)) := by
  dsimp only
  have h:=WilsonIndependentGroupedOrbit.original cloth z hz unit (f*g)
    (WilsonIndependentMatchedClosedPlan.product hf hg) W
  rw [←h,←Bare.normalized_scalar,WilsonOriginalPivotWardProduct.product _ hf hg]
  apply congrArg (Bare.normalized _ G)
  simp only [Bare.scalar,map_mul]
  ring

variable (R:Run G)(W:Initialize G)(Y:Sample 2)
local notation "T" => W.tree Y.F.p
local notation "F" d:max => R.family.labels.level d
variable {d D h H:ℕ}

def clearedDose (w:d<D)(v:Verse (F d))(b:Volume D)(s:Alma (F d)) : PowerSeries ℂ :=
  X^(WilsonPositionProgramMasterBirth.rank R (d:=d)-valence (F d) s) * dose R w v b s

theorem cleared (survey:Bool)(i:Fin 2)(w:d<D)(v:Verse (F d))(b:Volume D) :
    X^WilsonPositionProgramMasterBirth.rank R (d:=d)*word R W Y survey i w v b =
      ∑ s,Bare.scalar T (clearedDose R w v b s) *
        BareOrb.stencil T (placed R W Y survey d (Y.layout i) (sheet (F d) s)) := by
  rw [WilsonIndependentMatchedTopFilm.cleared]
  refine sum_congr rfl (fun s _=>?_ )
  rw [clearedDose]
  simp only [Bare.scalar,map_mul,map_pow,PowerSeries.map_X]

/-- Both marked leaves are integrated on the genuine enrolled inverted
Wilson fabric. The empty, scalar and marked-unit components stay in the
top verse, and the two slots share its one vacuum law. -/
theorem original (a c:Bool)(w:d<D)(w':h<H)(v:Verse (F d))(v':Verse (F h))
    (b:Volume D)(b':Volume H){𝓕:Fabric G Y.F.p.side}(cloth:𝓕.Cloth)
    (z:𝓕.Accounts→PowerSeries ℝ)(hz:∀slot,0<coeff 0 (z slot))(unit:z none=1) :
    X^(WilsonPositionProgramMasterBirth.rank R (d:=d)+WilsonPositionProgramMasterBirth.rank R (d:=h)) *
      Bare.normalized T G (word R W Y a 0 w v b*word R W Y c 1 w' v' b') =
      ∑ s, ∑ t, (clearedDose R w v b s*clearedDose R w' v' b' t) *
        TaylorWick.into (WilsonIndependentGroupedOrbit.paid cloth z hz
          (placed R W Y a d (Y.layout 0) (sheet (R.family.labels.level d) s) *
           placed R W Y c h (Y.layout 1) (sheet (R.family.labels.level h) t))) := by
  have outside (r s:ℕ)(A B:Bare.Series T G) :
      X^(r+s) * Bare.normalized T G (A*B) = Bare.normalized T G ((X^r*A)*(X^s*B)) := by
    rw [←Bare.normalized_scalar]
    apply congrArg (Bare.normalized T G)
    simp only [Bare.scalar,pow_add,map_mul,map_pow,PowerSeries.map_X]
    ring
  rw [outside,cleared,cleared,Finset.sum_mul,map_sum]
  refine sum_congr rfl (fun s _=>?_ )
  rw [Finset.mul_sum,map_sum]
  refine sum_congr rfl (fun t _=>?_ )
  exact row W cloth z hz unit _ _ (admitted R W Y a d _ _) (admitted R W Y c h _ _) _ _

end YM.Integration.WilsonIndependentMatchedTopPair
