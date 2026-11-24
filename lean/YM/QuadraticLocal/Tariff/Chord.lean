import YM.QuadraticLocal.Tariff.Stamps
import YM.Integration.LocalFormalCoefficients
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Tariff
open Function Filter Finset Lattice Wilson RG Ac Marker Push.Corrected Push.AbsoluteSums MeasureTheory
open RG3 RG3.Annuncia RG3.Ink Ovens Ovens.Pipes Progress.DirectedRecipe Fusion Attached Push.Local
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {p : BudgetPoint}
variable {V W : Type} [DecidableEq V] [Fintype V][DecidableEq W][Fintype W]
variable (u:W→ V) (R: Census V) (o : V→Site n)
local notation "S"=> (Annuncia.Replica u R)
local notation "ϕ"=> ( Annuncia.Replica.bill u R )
variable (γ:(Replica u R).Mode→ℂ)
variable (w:V→ℝ) (hw:∀ i,0<w i)
variable {T J η : Type*} {a b c δ ε :ℝ}{B B' :ℕ}
local notation "ν"=> ( w ∘ u )
open Comparison.RG02 Comparison.RG02.Order Comparison.RG02.Order.Join Comparison.RG02.Cumulants YM.Multi
open YM.Extra.Trajectories (connected)
-- projection polynomial table to ANY polar word by treating it as another axis; preserve θ component operators.Work.Frame.Param.Author.Engine.Volume
variable (r:ℕ)
local notation "Sr"=> (Replica u R)
def chord (i: Index r) : Grade R r→ₗ[ℂ] Poly R where
    toFun x:= Poly.inject fun s=> x.part ( Join.pair s i )
    map_add' _ _:=rfl
    map_smul' _ _:=rfl
local notation "μ"=> chord R r
lemma lift_part (x:Grade R r) (s:R.Mode) (i:Index r): ( (μ i) x).part s=x.part (Join.pair s i):=rfl
lemma chord_mul (x y:Grade R r) (i:Index r): (μ i) (x*y)= ∑ j:Index r,∑ k: Index r, if Poly.merges j k i then ((μ j) x)*(( μ k ) y) else 0:= by
    ext1 a; simp_rw [Poly.part_sum]; rw [lift_part,pair_product, sum_comm]; refine sum_congr rfl fun l h=>?_ -- sum_comm targets? sum over i j swapped at lhs
    have he(l' d:Index r) : (if Poly.merges l' d i then ( (μ l') x )*( ( μ d ) y ) else 0).part a=∑ t:R.Mode, ∑ s:R.Mode, if Poly.merges t s a ∧ Poly.merges l' d i then x.part ( Join.pair t l' )*y.part ( Join.pair s d ) else 0:= by
        by_cases hz: Poly.merges l' d i
        · simp only [hz,↓reduceIte,Poly.part_mul,lift_part,and_true] -- order
        simp only [hz, ↓reduceIte,and_false, Poly.part_nil,sum_const_zero]
    simp_rw [he]; conv_rhs=> rw [sum_comm];
    refine sum_congr rfl (fun i hi=>?_); rw [sum_comm]
lemma unit (i:Index r): (μ i) 1= if i=(indices r).quiet then 1 else 0:= by
    ext1 s; rw [lift_part,Join.one_pair]; by_cases h:i=(indices r).quiet <;> simp only [h,↓reduceIte,and_true,and_false, Poly.one_part,Poly.part_nil]

variable (g:W→ℂ)
local notation "Q"=> ( Replica.mouth u R g )
noncomputable def chamber : Grade (Replica u R) r →ₗ[ℂ] Grade R r where
    toFun x:= Poly.inject (fun s=> ( Q ((Tariff.chord (Replica u R) r (Join.right s)) x) ).part (Join.left s))
    map_add' x y:= by
       ext1 i; rw [Poly.part_plus]; refine Eq.trans (by rfl : _= (Q ((Tariff.chord (Replica u R) r (Join.right i)) (x+y))).part (Join.left i)) ?_; rw [_root_.map_add,_root_.map_add,Poly.part_plus]; rfl
    map_smul' t x:= by
       ext1 i; rw [ Poly.part_smul ]; change ( Q ( (Tariff.chord (Replica u R) r (Join.right i)) (t•x) ) ).part _= _ * (Q ( (Tariff.chord (Replica u R) r (Join.right i)) x )).part _;  rw [ _root_.map_smul, Replica.csmul, Poly.part_smul ]; rfl
local notation "H"=> (Tariff.chamber u R r g)
lemma refill (x:Grade (Replica u R) r) (s:R.Mode) (i:Index r): ( H x ).part (Join.pair s i)= (Q ((Tariff.chord (Replica u R) r i) x) ).part s:= by
    change (Q (( Tariff.chord (Replica u R) r ( Join.right ( Join.pair _ _ ) ) ) x) ).part ( Join.left _ )=_; rw [Join.right_pair,Join.left_pair]
lemma library (x:Grade Sr r) (i:Index r) : ( μ i ) (H x)= Replica.mouth u R g ( Tariff.chord (Replica u R) r i x ):= by ext1 v; exact Tariff.refill u R r g _ v _
lemma algorithm {x y:Grade R r}(h: ∀ z:Index r,( μ z ) x=( μ z ) y): x=y:= Join.both_parts (fun i z=> congr_arg ( fun a:Poly R=> a.part i ) (h z))
def alg : Grade Sr r →ₐ[ℂ] Grade R r:= AlgHom.ofLinearMap H (algorithm R r fun z=> by rw [library,unit,unit]; split <;> first| apply map_one | apply map_zero) (fun x y=> by
    apply algorithm R r; intro z; rw [library,chord_mul, chord_mul, _root_.map_sum]; refine sum_congr rfl fun j _=>?_ ; rw [_root_.map_sum]; refine sum_congr rfl fun t _=> ?_; split; rw [_root_.map_mul,library,library]; exact _root_.map_zero _ )
local notation "Φ"=> Tariff.alg u R r g
lemma law : (Φ).toLinearMap= H:= rfl
lemma quiet_alg (x): ( (Φ) x ).part (Board R r).quiet=x.part (Board (Replica u R) r).quiet:= by
    change ( H x ).part _= _; rw [← Join.pair_quiet («S»:=indices r) (R:=R),← Join.pair_quiet («S»:=indices r) (R:= Replica u R),refill, Replica.quiet,lift_part] -- S notation conflict! escape
lemma consecutive (x) (j:Index r): chord R r j (denominator x)= Poly.send R.quiet ((chord R r j x).part R.quiet):= by
    ext1 i; rw [lift_part,denominator,bottom_value,Poly.part_send]; split <;> first|rfl | next h=> rw [h]; rfl -- inspect
lemma coin (x:Grade Sr r): (Φ) (denominator x)=denominator ((Φ) x):= algorithm R r fun z=> by
    change (μ z) ( H _ )= (μ z) (denominator (H x)); rw [consecutive,library,library,consecutive, Replica.quiet, Replica.single]
lemma physical (x) (h:UnitLeading x): (Φ) ( Order.ratio x )= Order.ratio ((Φ) x):= by
    apply Order.ratio_unique ( show UnitLeading _ from (Tariff.quiet_alg u R r g x).trans h ); rw [ ← coin, ← map_mul, Order.recovers h ]
lemma marked (x) (h:UnitLeading x): (Φ) ( Order.logMarked x )= Order.logMarked ((Φ) x):= by rw [Order.logMarked, log_map Φ ( Tariff.quiet_alg u R r g ) (Order.ratio_quiet h), physical u R r g x h]; rfl
lemma vacuum (x) (h:UnitLeading x): (Φ) ( Order.logVac x )= Order.logVac ((Φ) x):= by rw [Order.logVac, log_map Φ ( Tariff.quiet_alg u R r g ) (show UnitLeading (denominator x) from (Order.bottom_quiet x).trans h), coin]; rfl
lemma observes (x:Grade (Replica u R) r) (i:ℕ): Order.observe R r ((Φ) x) i= Replica.mouth u R g ( Order.observe (Replica u R) r x i ):=by
   unfold Order.observe; split
   next h=> rw [Replica.csmul]; exact congr_arg ( (i.factorial:ℂ)⁻¹ • · ) ( Tariff.library u R r g x _ )
   next h=> exact (map_zero (Replica.mouth u R g)).symm
end YM.QuadraticLocal.Tariff
