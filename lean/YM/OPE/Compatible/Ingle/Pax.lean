import YM.OPE.Compatible.Ingle.Vine
import YM.OPE.Compatible.Tune.Theta
import YM.OPE.Compatible.Tune.Race
import YM.OPE.Compatible.Cant.Cadre
import YM.OPE.Compatible.Cant.Wiz
import YM.OPE.Compatible.Cant.View
import YM.OPE.Compatible.Cant.Nob
import YM.OPE.Compatible.Cant.Past
import YM.OPE.Compatible.Cant.Void
import YM.OPE.Compatible.Cant.Fat
/-!
# Factorization of the phase-zero reading through graded coordinates

`FundsGate` factors the phase-zero output through the coordinate map `Folt` and
the linear map `GateQ`. `GrovesK` shows that `gLift` is a right inverse for
`GateQ`, and `ReserveK` gives a polynomial growth bound for this lift.
`MintsQ` applies the same coordinate factorization to the labeled projection.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Stroke
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
open Quit.PriceZ Quit.Jac Quit Hark Topic StageLight
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P P':Patch}{R:ChartRatio G}{p p':Clip}
variable {v v' b u:ℝ}
variable {H:LocalRatio R}{hs:G.Simple}
open Balsam Nestle Pert.Full
variable {X:Sailing T P p R b}{B:Medal P G K.K P.J} {w:ℝ} {D₀:Stern K P τ l d w}(Hp: Alps.Crest G P K.K m)(Z:Topic H hs X B D₀)(a:Axis)
variable {Y:M→ℝ}
local notation "J!"=> Fin (l+1)
local notation "F!"=> Tracts G d τ
local notation "JΛ"=> Fin (l+1) 
open Pipes
local notation "μ"=>lapPrice (Patch.L P)
section
open GlowPack
variable (W:GlowPack Hp Z a (k:=k)) (U:Z.Ω M Y)(hq:1 ≤ Y)(hp:4 ≤ i)(V:(i':M)→Alps K T i (Y i'))
local notation "W!"=>Dux G l W.W
local notation "E!"=>Eagle Hp Z a W
variable {W Hp Z a U V} {hq hp}
variable (D:Cart Hp Z a W U hq hp V) (j':M)
open GlowPack
open Silt.Phere
local notation "V!*" => Drift.Turns D₀
noncomputable def GateQ : Folio G l→L[ℝ] OrthoC W:= by
       let T:bed G d (τ 0)→L[ℝ] F!:= ContinuousLinearMap.single (R:=ℝ) (fun i:Phase=> bed G (d+i.val) (τ i)) 0; exact (Energy 0 W).comp ((FirP D j').comp (T.comp (FolU D₀)))
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 200000
private lemma readAfterSection {E B A C : Type*} [AddGroup E] [AddGroup B] [AddGroup A]
    [AddGroup C] (out : E →+ C) (sample : E →+ B) (read : B →+ A)
    (put : B → E) (lift : A → B) (sample_put : ∀ b, sample (put b) = b)
    (read_lift : ∀ a, read (lift a) = a)
    (vanish : ∀ x, read (sample x) = 0 → out x = 0) (x : E) :
    out x = out (put (lift (read (sample x)))) := by
  let y := put (lift (read (sample x)))
  have h : read (sample (x - y)) = 0 := by
    rw [sample.map_sub, read.map_sub, sample_put, read_lift, sub_self]
  exact sub_eq_zero.mp ((out.map_sub x y).symm.trans (vanish (x - y) h))

private abbrev actualReadThrough :=
  let sample : Tracts G d τ →L[ℝ] bed G d (τ 0) := ContinuousLinearMap.proj 0
  readAfterSection ((Energy 0 W).comp (FirP D j')).toLinearMap.toAddMonoidHom
    sample.toLinearMap.toAddMonoidHom (Folt D₀).toLinearMap.toAddMonoidHom
    (fun b : bed G d (τ 0) => (Pi.single (0 : Phase) b : F!)) (FolU D₀)
    (fun b => by
      change (Pi.single (0 : Phase) b : F!) (0 : Phase) = b
      exact Pi.single_eq_same ..) (fLay D₀)
    (fun x hx => Lead_kill D j' x ((folThrough D₀ (x 0)).1 hx))

lemma FundsGate (x:F!):Energy 0 W (FirP D j' x)= GateQ D j' (Folt D₀ (x (0:Phase))):=by
  exact actualReadThrough D j' x
lemma FundsP (x:solar G d τ): Eψ D j' 0 x=GateQ D j' (Folt D₀ ((Fallix G D₀.aware K (V j').gear hp).symm x (0:Phase))):=FundsGate D j' _
noncomputable def ArkA (W:GlowPack Hp Z a (k:=k)) : OrthoC W→L[ℝ] LineCt W:=LinearMap.toContinuousLinearMap (LinearMap.pi fun i:J!=> (τ₀ (Eagle Hp Z a W i)).comp (LinearMap.proj i))
noncomputable def gLift : OrthoC W→L[ℝ] Folio G l:=by
       let A: Tracts G d τ →L[ℝ] bed G d (τ 0):= ContinuousLinearMap.proj 0
       exact (Folt D₀).comp (A.comp ((Pel D j').comp (ArkA W)))
private lemma initialCoordinate (q : OrthoC W) : Energy 0 W (ArkA W q) = q := by
  funext i
  exact τat _

private abbrev readLiftAgreement (x : OrthoC W) :=
  (FundsGate D j' (Pel D j' (ArkA W x))).symm.trans
    ((congrArg (Energy 0 W) (FitPel D j' (ArkA W x))).trans (initialCoordinate x))

lemma GrovesK (x:OrthoC W): GateQ D j' (gLift D j' x)=x:=by
  exact readLiftAgreement D j' x
lemma ReserveK : Wealth (fun j=>gLift D j) Y 1:=by
       let A: Tracts G d τ →L[ℝ] bed G d (τ 0):= ContinuousLinearMap.proj 0; exact PledgeW (wealthC (M:=M) (Folt D₀)) (PledgeW (wealthC A) (PledgeW (PelCost D) (wealthC (ArkA W)))) 
-- Apply the coordinate equivalence separately to the real and imaginary components.
private def pairedCoordinates {J : Type*} {A B : J → Type*}
    [∀ i, AddCommMonoid (A i)] [∀ i, Module ℝ (A i)]
    [∀ i, AddCommMonoid (B i)] [∀ i, Module ℝ (B i)]
    (v : ∀ i, A i ≃ₗ[ℝ] B i) :
    ((i : J) → A i × A i) ≃ₗ[ℝ] ((i : J) → B i) × ((i : J) → B i) where
  toFun p := (fun i => v i (p i).1, fun i => v i (p i).2)
  map_add' p q := by
    apply Prod.ext <;> exact funext fun i => (v i).map_add _ _
  map_smul' c p := by
    apply Prod.ext <;> exact funext fun i => (v i).map_smul _ _
  invFun p i := ((v i).symm (p.1 i), (v i).symm (p.2 i))
  left_inv x := funext fun i => Prod.ext ((v i).symm_apply_apply _) ((v i).symm_apply_apply _)
  right_inv x := Prod.ext (funext fun i => (v i).apply_symm_apply _)
    (funext fun i => (v i).apply_symm_apply _)

lemma φField {C:Register G}{S:Table C}{s:S.RealSpin}(W:GlowPack Hp Z a (k:=k))(h:Maxwell.Ranks S s): Nonempty (S.Field l ≃ₗ[ℝ] OrthoC W × OrthoC W):=by
  obtain ⟨f⟩ := SupportQ W.W (fun i => (W.trial.shares i).decmp) h
  exact ⟨f.trans (pairedCoordinates W.vnd)⟩
section
-- labelled projection and prices
open Spells
variable (U':BudgetPoint)(W':Source.Drops.Snap G l)(t:ℝ)
lemma FolCut (x:bed G d (τ 0))(h:Folt D₀ x=0): ζSig W' t U' d (τ 0) (sternCap D₀ 0).le x.val=0:=by
     rw [ζSig,_root_.sum_apply]; refine sum_eq_zero fun i _=>?_ ; rw [_root_.smul_apply,θFoil,_root_.sum_apply,sum_eq_zero,smul_zero]; intro j hj; rw [_root_.smul_apply, ΘCoin (k:=d) W' j x (by omega) (sternCap D₀ 0).le ((folThrough _ _).1 h), smul_zero]
lemma MintsQ (x:bed G d (τ 0)):
     let V:=ζSig W' t U' d (τ 0) (sternCap D₀ 0).le; V x.val= V (FolU D₀ (Folt D₀ x)).val:=by
        intro v; let u:=Folt D₀ x; let y:=FolU D₀ u; have he:Folt D₀ (x-y)=0:=by rw[map_sub,fLay,sub_self]; 
        rw [← sub_eq_zero,←_root_.map_sub]; exact FolCut U' W' t (x-y) he
end
end
end YM.OPE.Stroke
