import YM.Integration.WilsonMatrixTicketLanesRetainedBid
import YM.FormalOPE.RG10.MultiGauge.Degree

/-! Conditional connected quadratic words on the genuine finite retained Gaussian. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesRetainedPairMoments
open Function Filter MeasureTheory Finset Lattice Gauge PertExtension PertExtension.GaussianScore
open FormalOPE.RG10.MultiGauge FormalOPE.RG10.MultiGauge.Papers
open scoped Topology BigOperators Classical
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (Γ : Law E) (μ : Measure E) [μ.IsAddHaarMeasure]
local notation "Dual" => Module.Dual ℝ E
local notation "B" => opening μ Γ

def marked (e : Dual) : Permit E := ⟨e,linear e⟩

private theorem one (a : Dual) : B (marked a)=0 := by
  have got:=Γ.recursion μ a (fun _:Unit=>a) (∅:Finset Unit)
  simpa [Law.product,marked,opening] using got

private theorem two (a b : Dual) : B (marked a * marked b)=Γ.wick b a := by
  change Γ.average μ (fun y=>a y*b y)=_
  have got:=Γ.recursion μ b (fun _:Unit=>a) ({()}:Finset Unit)
  simp only [Finset.sum_singleton,Finset.erase_singleton] at got
  rw [show Law.product (fun _ : Unit=>a) ∅=1 from funext (fun _=>Finset.prod_empty),Γ.empty μ] at got
  simpa [Law.product,marked,opening] using got

private theorem three (a b c : Dual) : B (marked a*marked b*marked c)=0 := by
  change Γ.average μ (fun y=>a y*b y*c y)=_
  let t: Fin 2→Dual:=![a,b]
  have got:=Γ.recursion μ c t Finset.univ
  have e₀ : (Finset.univ : Finset (Fin 2)).erase 0 = {1}:=by decide
  have e₁ : (Finset.univ : Finset (Fin 2)).erase 1 = {0}:=by decide
  have atom (q : Fin 2→Dual) (i : Fin 2) : Γ.average μ (Law.product q {i})=0:=by
    have eq : Law.product q {i}=(fun y=>q i y):=by funext y;exact Finset.prod_singleton _ _
    rw [eq];exact one Γ μ (q i)
  rw [Fin.sum_univ_two,e₀,e₁,atom,atom] at got
  simpa [t,Law.product,Fin.prod_univ_two] using got

private theorem four (a b c d : Dual) : B (marked a*marked b*marked c*marked d) =
    Γ.wick c b*Γ.wick d a + Γ.wick c a*Γ.wick d b + Γ.wick b a*Γ.wick d c := by
  change Γ.average μ (fun y=>a y*b y*c y*d y)=_
  let t: Fin 3→Dual:=![a,b,c]
  have got:=Γ.recursion μ d t Finset.univ
  have e₀ : (Finset.univ : Finset (Fin 3)).erase 0 = {1,2}:=by decide
  have e₁ : (Finset.univ : Finset (Fin 3)).erase 1 = {0,2}:=by decide
  have e₂ : (Finset.univ : Finset (Fin 3)).erase 2 = {0,1}:=by decide
  have pair (i j : Fin 3) (neq : i≠j) : Γ.average μ (Law.product t {i,j})=Γ.wick (t j) (t i):=by
    have eq : Law.product t {i,j}=(fun y=>t i y*t j y):=by funext y;simp [Law.product,neq]
    rw [eq];exact two Γ μ (t i) (t j)
  rw [Fin.sum_univ_three,e₀,e₁,e₂,pair 1 2 (by decide),pair 0 2 (by decide),pair 0 1 (by decide)] at got
  simpa [t,Law.product,Fin.prod_univ_three,mul_assoc] using got

/-- The two conditional Wick contractions between the marked pairs persist at zero pin.
At an arbitrary retained field four more terms, each with one crossed contraction, are observable. -/
theorem quadratic (a b c d : Dual) (s : E) :
  Γ.average μ (fun y=>(a (y+s)*b (y+s))*(c (y+s)*d (y+s))) -
    Γ.average μ (fun y=>a (y+s)*b (y+s))*Γ.average μ (fun y=>c (y+s)*d (y+s)) =
  Γ.wick c b*Γ.wick d a + Γ.wick c a*Γ.wick d b +
    a s*c s*Γ.wick d b + a s*d s*Γ.wick c b + b s*c s*Γ.wick d a + b s*d s*Γ.wick c a := by
  let line (z : Dual):Permit E:=marked z+(z s)•1
  have read (z : Dual) (y : E) : (line z).val y=z (y+s):=by change z y+z s*1=_;rw [mul_one,map_add]
  have pair (u v : Dual) : B (line u*line v)=Γ.average μ (fun y=>u (y+s)*v (y+s)):=by
    apply congrArg (Γ.average μ);funext y;change (line u).val y*(line v).val y=_;rw [read,read]
  have bill : B ((line a*line b)*(line c*line d))=Γ.average μ (fun y=>(a (y+s)*b (y+s))*(c (y+s)*d (y+s))):=by
    apply congrArg (Γ.average μ);funext y;change ((line a).val y*(line b).val y)*((line c).val y*(line d).val y)=_;simp only [read]
  rw [←bill,←pair,←pair]
  simp only [line,mul_add,add_mul,mul_smul_comm,smul_mul_assoc,mul_one,one_mul,←mul_assoc,
    map_add,map_smul,smul_eq_mul,one,two,three,four,starts,mul_zero,mul_one,one_mul,add_zero,zero_add]
  ring

end YM.Integration.WilsonMatrixTicketLanesRetainedPairMoments
