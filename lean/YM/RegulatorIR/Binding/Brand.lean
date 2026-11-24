import YM.RegulatorIR.Binding.Melody

/-! Translate the integrand polynomial chart in one dimension step.
Scalars normalized with the same Wick operand regardless of insertion.
*No* finite-box Laplace constants in the polynomial-history budget. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Binding
open PertExtension Laplace Chart Lattice Geometry Orb Gauge MeasureTheory Filter Function Set Metric Exterior Wilson RG Series Series.Radial Series.Tested Diagram.Formal Diagram Diagram.Gaussian Budget Budget.Packet Budget.Layer Budget.Tuple PowerSeries GaussianScore
open scoped ContDiff Topology NNReal ENNReal BigOperators Classical PowerSeries
variable {G:Gauge}{E I J L X Y Z:Type}[Fintype E][Fintype I][Fintype J][Fintype L][Fintype X][Fintype Y][Fintype Z]
variable {m:ℕ} {T:Viewport G I}{Q:Viewport G J}{W:Transfer I L G}{F M:Hook G E I}
  {R: Hook G L J} {s:ℕ} {P:Medium G I Y}{N:Medium G J Z}{a:Y↪X}{b:Z↪X}{A B: Layer X X}{U:Orders X}

def rangeX (w:X→ℝ)(f:PowerSeries (Jet X)):= PowerSeries.map (emphasis w).toRingHom f

namespace Clip
variable (C:Clip (V:=W) (F:=R) P N a b A B U)
variable (h:Stead T F)(hp:Move T Q W R)
-- avoid x type conflicts

def hearX (w:Meadow G J)(x : Meadow G L) := announce B (dilute b (N.color w))+ fun i=> C.directions i x

def pairing (w: Meadow G J)(x: Meadow G L)(M:Hook G E I) (F:Hook G E I): ℝ⟦X⟧:= manuscript F M (W.curve (x+C.slide w)) * PowerSeries.mk (fun i=> normTerm (aura (1:Hook G L J)) (priceMap R) i (x+C.slide w,1,w))
-- varying step Dir,G included in C

include h hp in
omit [Fintype Y] [Fintype Z] in
lemma cashThrough (hM:Tune M) (Λ:ℝ⟦X⟧)(Q':PowerSeries (Jet X))(w:Meadow G J)
 (hQ:∀ x,C.pairing w x M F = PowerSeries.C (C.law.kern x)* (Λ * rangeX (C.hearX w x) Q')) : manuscript (fuse W F R) (blade J W M) w= Λ * PowerSeries.C (sizes C.law)* Diagram.burn C.law C.directions (tangent G L) Q' (announce B (dilute b (N.color w))) := by
 ext1 e
 let K:=C.hearX w; let g:= announce B (dilute b (N.color w)); let H:=C.law; let v:= C.directions;let μ:=tangent G L; let z:=C.slide w
 rw [manuscript, PowerSeries.coeff_mk,heard h hp hM];
 let f (i:Meadow G L):= conv (tomorrow F M (W.curve i)) (fun j=> normTerm (aura (1:Hook G L J)) (priceMap R) j (i,1,w)) e
 rw [show (∫ x:Meadow G L,f x ∂tangent G L) = ∫ x,f (x+z) ∂tangent G L from (integral_add_right_eq_self ..).symm] -- defeq rw?
 let T i:= probe v g (coeff i Q'); let u (i j: ℕ):= fun x: Meadow G L=> coeff i Λ*(T j x * H.kern x)
 have he (x:Meadow G L): f (x+z)=∑ i∈Finset.antidiagonal e,u i.1 i.2 x:=by
    change coeff e (C.pairing w x M F)= _
    rw [hQ,PowerSeries.coeff_C_mul,coeff_mul, Finset.mul_sum]; apply Finset.sum_congr rfl;intro i _
    unfold rangeX; rw [PowerSeries.coeff_map]; change H.kern x*(_ * emphasis _ _)= _
    rw [language]; change H.kern x*(coeff i.1 Λ*T i.2 x)=_ ; unfold u; ring
 simp_rw [he]; rw [integral_finsetSum, mul_assoc,PowerSeries.coeff_mul];apply Finset.sum_congr rfl;intro i _
 rw [PowerSeries.coeff_C_mul,Diagram.burn,PowerSeries.coeff_mk]
 unfold u; rw [integral_const_mul]; apply congr_arg
 rw [averaged, Law.average,sizes,mul_div_cancel₀]; rfl
 exact (sizes_pos C.law).ne'
 intro i _; exact (Diagram.Gaussian.accept H v g μ (coeff i.2 Q')).const_mul _

variable {D E':Orders Y}{ξ:ℝ⟦X⟧}

def direction (_C:Clip (V:=W) (F:=R) P N a b A B U)(ξ:ℝ⟦X⟧)(w:Meadow G J):ℝ⟦X⟧:= PowerSeries.C (Real.exp (-N.kinetic w))*ξ*PowerSeries.C (morning G L)
-- avoid unused C
variable (D':Dusk s F M P D ξ E' m)
include D'
omit [Fintype Z] in
lemma combination (w: Meadow G J) (x: Meadow G L) : C.pairing w x 1 F=PowerSeries.C (C.law.kern x)*(C.direction ξ w *rangeX (C.hearX w x) (expo (rated (fun e=>e+2) (supply D a U)))):=by
 unfold pairing; rw [C.sing,D'.bare]
 let K:= C.hearX w x;let P':= W.curve (x+C.slide w)
 have hx: rangeX K (expo (rated (fun e=>e+2) (supply D a U))) = expo (flavor 2 (P.color P') D)*expo (flavor 2 K U):=by
   unfold rangeX;rw [Formal.map_exp];change expo (flavor 2 K (supply D a U))=_;rw [supply,flavor_add,← show flavor 2 (P.color P') D= flavor 2 K (Cluster.present a D) from C.offerP D 2 w x]
   exact timble_exp (flavor_dark _ (vacuum_lo _ D'.vacuum) _) (flavor_dark _ (vacuum_lo _ C.order) _)
 let z:=(x + C.slide w,(1:ℝ),w); let q:= jet (priceMap R) 2 z
 let Φ:=morning G L;let O:= expo (flavor 2 (P.color P') D);let Y':=expo (flavor 2 K U)
 have hS: Real.exp (-P.kinetic P')*(Φ *Real.exp (-q)) = C.law.kern x * (Real.exp (-N.kinetic w)*Φ) := by
    rw [show Real.exp _*(Φ*_)=Φ*(Real.exp (-P.kinetic P')*Real.exp (-q)) by ring,
       Law.kern,mul_comm Φ,← mul_assoc _ _ Φ,← Real.exp_add,← Real.exp_add]
    apply congr_arg (· * Φ); apply congr_arg; unfold P' q z; linarith [C.gap w x]
 rw [show rangeX _ _= _ from hx]; change PowerSeries.C _ * ξ * O * (PowerSeries.C (Φ*Real.exp (-q))* Y')=PowerSeries.C _*(_*(O*Y'))
 unfold direction
 calc
    _=PowerSeries.C (Real.exp (-P.kinetic P')*(Φ*Real.exp (-q)))*ξ*(O*Y'):= by simp only [map_mul]; unfold P'; ring
    _ = _:=by rw [hS,map_mul,map_mul]; change _=PowerSeries.C _*(PowerSeries.C _*ξ*PowerSeries.C Φ*(O*Y')); ring
omit [Fintype Z] in
lemma combination_mark (w:Meadow G J) (x : Meadow G L) : C.pairing w x M F=PowerSeries.C (C.law.kern x)*(C.direction ξ w*PowerSeries.X^s * rangeX (C.hearX w x) ((expo (rated (fun e=>e+2) (supply D a U)))*rated (fun i=>i+m) (Cluster.present a E'))):=by
 let K:=C.hearX w x; let f:= Cluster.present a E'; let V:= flavor m (P.color (W.curve (x+C.slide w))) E'; let Φ:=expo (rated (fun e=>e+2) (supply D a U))
 have hp : V = rangeX K (rated (fun i=>i+m) f) := C.offerP E' m w x
 rw [show C.pairing w x M F = C.pairing w x 1 F * (PowerSeries.X^s*V) from ?_, C.combination D' w x]; unfold rangeX; rw [hp,map_mul]; unfold rangeX K f; ring
 unfold pairing; rw [D'.stamped]; unfold V;ring
end Clip
end YM.RegulatorIR.Binding
