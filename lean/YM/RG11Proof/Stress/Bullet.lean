import YM.RG11Proof.Stress.Horizontal

/-!
# Two finite-arity microphones, conservation gradient and translation flux

Applied to coefficient distributions of ShapeReport; to consume stress
normalize laws which use functions instead, via `Tangible` in the scheme's
SMOOTH domain. Capable also of relating derivative point reports in general.
Distributed probes multiply left (complex-linear), sign conventions Table
(from Euclid/Stress.lean), project stress candidate a,b -> Taps. No assuming
that actual evaluated contacts follow these equations.
-/
set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.RG11.Stress
open YM.RG11.Fields YM.RG11.Jets YM.RG11.Nodes
open scoped Topology ContDiff Classical BigOperators
open Maxwell Labels Table Climb Work.A01 Next.UVStress UVNext.FreeStress Function Filter Set MeasureTheory Analysis Pert.Position
open PowerSeries
variable {G:Gauge}{F:Frames G}(A:ShapeReport G F)

-- reusable reading evaluation
def voice {d n}(v:Fin n→ E F d)(k:ℕ):spot n where
  toFun f:= A.table k d n f v
  map_add' f g:=by rw [map_add]; rfl
  map_smul' z f:=by rw [map_smul]; rfl

def sang {d n}(B:Basis F d)(k:ℕ)(v:Fin n→B.J):spot n:=voice A (B.b ∘ v) k

def survey {d n}(B:Basis F d)(f:clean n→ₗ[ℂ] ℂ): reading B.J (PowerSeries ℂ) n:= perceive (sang A B) (lift f)

 theorem site_smooth {n}(v:Fin n→E F 4):ContDiffOn ℝ ∞ (site F v) (conf n):=(freeTable F).class_smooth _ (Maxwell.table_smooth F) (fourWord F v)

 theorem origin4 {n}(v:Fin n→E F 4): voice A v 0=pour n (dress (site F v) (site_smooth v)):=by
   ext1 f; rw [mixes]; change A.table 0 _ _ f v=_; rw [A.maxwell]; rfl

 theorem survey_zero4 (B:Basis F 4){n}(v:Fin n→B.J)(f:clean n→ₗ[ℂ] ℂ): constantCoeff (survey A B f v)=f (dress (site F (B.b ∘ v)) (site_smooth _)):=by
   simp_rw [survey,perceive,constantCoeff_mk,sang,origin4,lift_at]

 theorem survey_match {e}(Z:Basis F e)(B:ShapeReport G F){N}{p:Change ℝ Z.J}(hp:Anchored p.g)
    (h:∀ z,Through N (p.act (A.realAt Z) z) (B.realAt Z z)){n}(v:Fin n→Z.J)(f:clean n→ₗ[ℂ] ℂ):
     Through N (plant (toComplex p).Z (fun w=>PowerSeries.subst (toComplex p).g (survey A Z f w)) v) (survey B Z f v):=by
   have he:=ShapeReport.match_full B Z hp (fun v=>(h v).symm)
   apply extend_questions (p:=toComplex p) (deposit_base p.g hp) (fun x q=>?_) (lift f)
   exact (he ⟨⟨n,x⟩,q⟩).symm

-- Press microphone head arity n+1, only incoming stress response direction zero

def shellers {n}(K:Axis→(clean (n+1)→ₗ[ℂ] ℂ))(j:Taps):clean (n+1)→ₗ[ℂ] ℂ:= if j.2=0 then K j.1 else 0

def direct(a:Axis):clean 2→ₗ[ℂ] ℂ:= directional (n:=2) 0 a (shutter 0)
def traded{χ:E4→ℝ}(w:Window (camera 0) χ)(a:Axis):clean 3→ₗ[ℂ] ℂ:=run (n:=1) (shutter 0) w a

-- Ward tests labelled. Choose Sd∈ps(Taps×B.J) which is centered by convention
-- first, maintains vacuum qualification; call `Signals`. No theorem of
-- deriving this stress from Wilson or MS prescription normalization yet.
abbrev psStress (B:Basis F 4) := Rect Taps B.J (PowerSeries ℝ)

def shine (B:Basis F 4)(T:psStress B):Rect Taps B.J (PowerSeries ℂ):=T.map Jets.deposit

def queryHeads (B:Basis F 4){n}(K:Axis→(clean (n+1)→ₗ[ℂ] ℂ)):facets Taps B.J ℂ n:=fun i=>survey A B (shellers K i)

structure Signals (B:Basis F 4)(T:psStress B)(N:ℕ){χ:E4→ℝ}(hw:Window (camera 0) χ): Prop where
   diverges : Mandate (shine B T) (queryHeads A B direct) (survey A B (n:=1) 0) N
   translates : Mandate (shine B T) (queryHeads A B (traded hw)) (survey A B (directional (n:=2) 0 0 (shutter 0))) N

/-- arbitrary power order k. For tangible independent coefficient kernels incl
power>0, these functionals really evaluate the stated differential readings.
-/
 theorem survey_integrated {d}(B:Basis F d){n}(v:Fin n→B.J)(k:ℕ)(ψ:clean n→ₗ[ℂ] ℂ){K:Points n→ℂ}
    (h:ContDiffOn ℝ ∞ K (conf n))(hf:∀ f:Test n,A.table k _ _ f (B.b ∘ v)=f.applyTo K):
      coeff k (survey A B ψ v)=ψ (dress K h):=by
   have he:sang A B k v=pour n (dress K h):= LinearMap.ext fun f=>(hf f).trans (mixes K h f).symm
   simp_rw [survey,perceive,coeff_mk,he,lift_at]
end YM.RG11.Stress
