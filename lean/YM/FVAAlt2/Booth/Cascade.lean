import YM.FVAAlt2.Booth.Prices
import YM.FVAAlt2.Lyric.Census
/-! # Kernel.Persector full period. Definitions for paid periods of any actual chain. Drift matrix linear χ frame peg with right sign. Computes SAME parameters as absolute Charter. Use blow with actual stencil arguments. Pack.L.Every Cover Replica convergence separately. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.FVAAlt2.Booth.Arm
open Function Finset MeasureTheory Filter Set Budget Budget.Layer Budget.Packet Budget.Tuple Budget.Deck Motion Matrix Prim PertExtension Series Series.Radial Series.Tested Chart Lattice Tree Gauge Binding Diagram Diagram.Formal RG Wilson Oracle Geometry Quadratic
open PowerSeries Exterior Precision Bid Comparison.RG02 Comparison.RG02.Bulk Comparison.RG02.Adjacent Comparison.RG02.FVAAlt2 Integral
open FreeResolvent (tensor flatten)
open scoped ENNReal NNReal Topology BigOperators Classical PowerSeries ContDiff Matrix Matrix.Norms.Frobenius
variable {c f n:Side}{G:Gauge}{p: RG.Clip}{O:ChartRatio G}{U:PathData G}
variable (S:StepData c f)(F:Forest S.ratio) (L: Binding.Scale) (H:S.patch.Branches S.kernel G)
local notation "X"=>fieldDir G c 1
local notation "Y"=>fieldDir G f 1
local notation "T"=> Comparison.RG02.Bulk.Joint S F (G:=G)
local notation "Q"=>Pins f c G
local notation "E"=> Precision.Key F G
local notation "J"=> directive S
local notation "Y'" => Pin f G
local notation "X'"=> Pin c G
variable (K: Comparison.RG02.Bulk.Kernel S p U O)(C:UnitCost) (w:Geometry.Field.Square F)

-- full periodic (analogue of Reel Grid). no deck issues
def inventory (n:Side)(G:Gauge): fieldDir G n 1≃ₗ[ℝ](Pin n G → ℝ) where
   toFun:= flatten
   invFun f:= fun i=> WithLp.toLp 2 (fun j=>f (i.1,i.2,j))
   left_inv _:=rfl
   right_inv _:=rfl
   map_add' _ _:=rfl
   map_smul' _ _:=rfl

def high : X →ₗ[ℝ] (Pin f G → ℝ):= ( inventory f G ).toLinearMap.comp (( LinearMap.snd ℝ X Y ).comp (( Aperture.alpha F ).toLinearMap.comp (( LinearMap.id (M:=X)).prod ((fderiv ℝ (K.b F) 0).toLinearMap)))) -- notation uses abstract. fix
lemma high_g (x:X): high S F K x= flatten ( stretch F (classical S F (K.b F) x) ):= congr_arg (fun t=> flatten (Prod.snd t)) (Aperture.uniting_eq F (stage K F x))

def Pred := LinearMap.toMatrix' ((high S F K).comp ((inventory c G).symm.toLinearMap))
def driftM: Layer (Pins f c G) (Pins f c G) := Function.swap (hoses ( Pred S F K ))
def riseM : Matrix (Pin f G) (Precision.Key F G) ℝ:= FreeResolvent.insertion (FreeResolvent.plant F (G:=G))
def kickA: Matrix (Pins f c G) (Precision.Key F G) ℝ:= Sum.elim (riseM S F) (fun _=>0)
def night : Layer (Pin f G) (Pin f G) := (show Matrix (Pin f G) (Pin f G) ℝ from riseM S F (G:=G) *K.covariance F (directive S) * (riseM S F (G:=G))ᵀ ) -- instance DecidableEq issues
local notation "μ"=> K.covariance F (directive S)
local notation "κ"=> night S F K
def spins:= petals (κ) (I:=Pin c G)
lemma intensity : spins S F K= (show Matrix Q Q ℝ from kickA S F (G:=G) * μ * ( kickA (G:=G) S F )ᵀ):=by
    let F':= kickA S F (G:=G); let T':= petals κ (I:=Pin c G); have hp: ∀ i:Pin c G, ∀ j:Precision.Key F G,F' (.inr i) j=0:=fun _ _=> rfl
    have ht(x): ∀ i:Pin c G,(F'*μ) (.inr i) x=0:=by intro i; rw [Matrix.mul_apply]; simp_rw [hp,zero_mul,sum_const_zero]
    refine Matrix.ext (M:=(show Matrix Q Q ℝ from spins S F K)) ?_; intro x y
    change T' x y=(F'*μ*F'ᵀ) x y
    cases x with
    | inl x=> cases y with
        | inl y=> rfl
        | inr y=> rw [Matrix.mul_apply]; simp only [ Matrix.transpose_apply,hp,mul_zero,sum_const_zero ]; rfl
    | inr x => rw [Matrix.mul_apply]; simp_rw [ht _ x,zero_mul,sum_const_zero]; cases y <;> rfl

def environment (x:X):=(Tape.announceT (Aperture.uniting F (stage K F x)))
abbrev offshoot : Pin c G ↪ Q:= Function.Embedding.inr
lemma enters (x:X): Diagram.announce (driftM S F K) (Diagram.dilute (offshoot (G:=G) (f:=f) (c:=c)) (flatten x))= environment S F K x:=by
    let P:= driftM S F K; let U':= Diagram.dilute (offshoot (f:=f)) (flatten x)
    have h(i:Pin c G): U' (.inr i)= flatten x i := Diagram.dilute_here (offshoot (G:=G) (f:=f)) _ i
    have hz(i:Pin f G): U' (.inl i)=0:= Diagram.dilute_miss _ _ _ (by rintro ⟨k,hk⟩; cases hk)
    have hl : Pred S F K *ᵥ flatten x= high S F K x:=by rw [Pred]; rw [LinearMap.toMatrix'_mulVec] ; rfl
    ext1 i; change ∑ y, P y i*U' y= Tape.announceT (Aperture.uniting F (stage K F x)) i
    rw [Fintype.sum_sum_type,Tape.traverseT]; simp_rw [hz,mul_zero,sum_const_zero,h,zero_add]
    cases i with
    | inl y => exact congr_fun (hl.trans (high_g S F K x)) y -- need high_g
    | inr y=> change ∑ j:Pin c G, ID (Pin c G) y j*_= flatten x y; simp [ID] -- foo
lemma arrive (x:X)(v:E→ℝ) : environment S F K x+ kickA S F*ᵥ v=Tape.announceT ( Aperture.uniting F ( translated K F x v ) ) :=by
    ext1 i; cases i with
    | inl i=>
       unfold environment translated Assembly.translate; rw [_root_.map_add]; let Xₐ:=Aperture.uniting F (hinge F (G:=G) v)
       have he(i):kickA S F (G:=G) (.inl i)=riseM S F i:=rfl
       have hp : riseM S F*ᵥ v= flatten Xₐ.2:=by
           unfold Xₐ; rw [Aperture.uniting_eq]; exact FreeResolvent.chart_flow S F (Next.SectorChange.tape v)
       exact congr_arg₂ (· + ·) (rfl : _= Tape.announceT (Aperture.uniting F (stage K F x)) (Sum.inl i)) (congr_fun hp i)
    | inr i=>
       have ht : kickA S F (.inr i) ⬝ᵥ v=0:=sum_eq_zero fun j _=> zero_mul _
       unfold environment translated Assembly.translate; rw [Pi.add_apply,_root_.map_add,show (kickA S F*ᵥ v) (.inr i)=0 from ht,add_zero]; have hu: (Aperture.uniting F (Bulk.hinge F v)).1=0:=by rw [Aperture.uniting_eq];rfl
       change _= flatten ( _+(Aperture.uniting F (Bulk.hinge F v)).1) i; rw [hu,add_zero]; rfl
end YM.RegulatorIR.FVAAlt2.Booth.Arm
