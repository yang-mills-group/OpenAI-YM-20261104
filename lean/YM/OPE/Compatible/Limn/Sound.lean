import YM.OPE.Compatible.Limn.Kings
/-!
# Full-restriction regression. Actual support, no arbitrary conditional boxes.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Limn
open Function Filter Set MeasureTheory Lattice Laurent RG Matrix Precision Exterior Tree Push Push.AbsoluteSums Wilson Woody
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {G:Gauge}{c f:Side}{X Y V:Type}
open Next.SectorChange Next.SectorChange.Schur PertExtension Series Libra GaussianScore Flume Flume.Page Flume.Script Flume.Virgin Zeph
open AnalyticNext.QuarticMatch Radius Estimate Radius.Articles Radius.Polish Radius.Fetch Radius.Showroom AnalyticNext.QuarticMatch.Local
open Cascade Rill Votive Stationary Progress.StationaryScenes Work.F03 Next.Free Work.F05 Glass Coin Pilot Next.Foundations Work.F08 FreeResolvent
open PhysicalNext.Repeat.Aroma
variable {t r R B b ε:ℝ}{m:ℕ}
variable {S:StepData c f}{F:Forest S.ratio} {I:Seats F}
open Finset Module
local notation "Wk!"=> Module.Dual ℝ
section
variable [Fintype X][NormedAddCommGroup V][NormedSpace ℝ V][FiniteDimensional ℝ V](A:Basis X ℝ V) {C:Matrix X X ℝ}(B:Law V)
abbrev Trained (A:Basis X ℝ V)(C:Matrix X X ℝ)(B:Law V):Prop:=∀ x y,B.P x y= cash A x ⬝ᵥ (C *ᵥ cash A y)
variable (h:Trained A C B)
omit [FiniteDimensional ℝ V] in
lemma cashOne [DecidableEq X](i:X): cash A (A i)=Pi.single i 1:=funext fun j=>by simp [cash,Pi.single_apply,eq_comm]
include h
lemma longW [DecidableEq X](hc:C.PosDef)(f:Wk! V): cash A (B.inverse f) = C⁻¹ *ᵥ (fun i=> f (A i)):=by
      have he : IsUnit C.det:=(C.isUnit_iff_isUnit_det).mp hc.isUnit; suffices hp : C *ᵥ cash A (B.inverse f)=fun i=> f (A i) by rw [← hp, mulVec_mulVec, Matrix.nonsing_inv_mul _ he, one_mulVec]
      funext i; have h0:= h (A i) (B.inverse f); rw [cashOne,B.turns,B.applies] at h0; simpa using! h0.symm
omit h [FiniteDimensional ℝ V] in
noncomputable abbrev castAt (i:X):Wk! V:= LinearMap.proj i ∘ₗ (cash A).toLinearMap
lemma coverage [DecidableEq X](hc:C.PosDef)(i j:X): B.wick (castAt A j) (castAt A i)= C⁻¹ i j:=by
       change cash A (B.inverse _) i=_; rw [longW _ B h hc,show (fun i:X=> castAt A j (A i))=Pi.single j 1 from ?_]; simp
       funext k; change cash A (A k) j=_; rw [cashOne]; simp [Pi.single_apply,eq_comm]
end
variable (S F)
local notation "K!"=> Key F G
variable (B:Matrix (Key F G) (Key F G) ℝ)(Z:Law (AxisChart G F))(h:Trained (countingBasis F G) B Z) (I)
local notation "Tp"=>Tip G (I : Type)
noncomputable abbrev ChartUp := dimT (stake I) Z (bit I Z)
include h
noncomputable abbrev plateK (B:Matrix (Key F G) (Key F G) ℝ):Matrix (Rubric G I) (Rubric G I) ℝ:=B.submatrix (shout G I) (shout G I)
lemma WithK: Trained (Tip G (↥I)) (plateK S F I B) (bit I Z):=by
       intro x y; rw [inflect,h, chunk,chunk,entr]; change cash _ x ⬝ᵥ _=_; apply congr_arg (cash _ x ⬝ᵥ ·); ext i; rw [Function.comp_apply, mulVec,dotProduct_comm, entr, mulVec,dotProduct_comm];rfl
lemma Highway (hb: B.PosDef)(p:AxisChart G F):
       cash (Tip G (↥I)) (ChartUp S F I Z p) = (plateK S F I B)⁻¹ *ᵥ ((B *ᵥ cash (countingBasis F G) p)∘shout G I):=by
           change cash _ ((bit I Z).inverse ((Z.P p).comp _)) =_; rw [longW (V:=Keys G (↥I)) _ _ (WithK S F I B Z h) (hb.submatrix (shout G I).injective)]; apply congr_arg; funext i; change Z.P p (stake I _) = _; rw [tipS,Z.turns,h, cashOne]; simp
-- R monotone
noncomputable def clipRail (B:Matrix (Key F G) (Key F G) ℝ): Matrix (Rubric G I) (Key F G) ℝ:= (plateK S F I B)⁻¹ * (B.submatrix (shout G I) id)
lemma hop (hb:B.PosDef)(p:AxisChart G F) : cash Tp (ChartUp S F I Z p)=(clipRail S F I B) *ᵥ cash (countingBasis F G) p:=by rw [Highway S F I B Z h hb,clipRail,←mulVec_mulVec];rfl
lemma boots (hb:B.PosDef)(i j:Rubric G I):clipRail S F I B i (shout G I j)=if j=i then 1 else 0:=by
       let y:= countingBasis F G (shout G I j); have he: stake I (Tip G (↥I) j)= y:= tipS j; have he' := dryW (stake I) Z (bit I Z) (inflect _ _) (Tip G (↥I) j); rw [he] at he'; have hh := congr_fun (hop S F I B Z h hb y) i; rw [show ChartUp S F I Z y= _ from he',cashOne,cashOne (countingBasis F G)] at hh; simpa [eq_comm, Pi.single_apply] using hh.symm -- simp
end YM.OPE.Limn
