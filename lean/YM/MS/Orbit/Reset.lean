import YM.MS.Orbit.Mat
/-!
# Effective vertex palette operations, including the anchor image extensions. Site fraction.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Orbit
open Set Function Filter Finset Metric MeasureTheory
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Snap Native Lattice City Latch Flux
open scoped Topology ContDiff Interval
variable {I E:Type}{G:Gauge}{n:Side}{P Q:Latch.Edge G}{F H: Law G}{w x y:Lengths G}{A: Cover}{μ:Measure QP}
abbrev Opp (b:Bool): QP→QP:= if b then id else Neg.neg
abbrev taste (b:Bool)(p:Cover): Cover:= if b then p else -p -- Asc position sign, use $riseB(P) := A+taste b B`
abbrev be (A:Cover)(p:QP):= bill (embed A) p
def Θ_pc (b:Bool)(μ:Measure QP)(A:Cover)(P:Latch.Edge G) (F:Law G): Law G:= fun l=>∫ q, be A q * (∑ i:BH G,∑ j:BH G, P i j q * F ((i,q)::(j,Opp b q)::l)) ∂μ
def viν (b:Bool) (X:Latch.Edge G)(i j:BH G)(x:Law G)(y:Law G)(l k:Lengths G)(q:QP):= 2 * X i j q *((cross (parity j) (degree (field parity) l):ℂ)* x ((i,q)::l))* y ((j,Opp b q)::k)
def PairV (b:Bool)(μ:Measure QP)(A B:Cover)(P: Latch.Edge G)(F H:Law G): Law G:=fun w=> scatter (field parity) w (fun l r=> be A (net l) * (∑ i:BH G,∑ j:BH G,∫ q, be B q * viν b P i j F H l r q ∂μ))
-- born at each fixed-site defect from image tadpole. use q duplicated.
def detach (P: Latch.Edge G) (F:Law G) (l:Lengths G)(q:QP):= ∑ i:BH G,∑ j:BH G,P i j q * F ((i,q)::(j,q)::l)
def birth (P: Latch.Edge G)(F: Law G): Law G:= fun l=> (1/16:ℂ) * Hβ (detach P F l) (net l)
-- period rules
lemma Θ_per (p b c v)(h:Speaks F): Speaks (Θ_pc b p v c F):= fun x y hp=> by unfold Θ_pc; simp_rw [ show ∀ i j:Lane4 G,F (i::j::x)=F (i::j::y) from fun i j=> h _ _ ( .cons ⟨rfl,congrQ.normal _⟩ (.cons ⟨rfl,congrQ.normal _⟩ hp) ) ]
lemma φ_per (A:Cover): pinQ ( be A ):= by intro p q he; unfold be; rw [rights,rights (embed A) q]; exact pin_pay A he
lemma eye (b i j z)(hx:Speaks F)(hv:Speaks H) (w x y a)(h:twins w y)(he:twins x a) (q:QP) : viν b z i j F H w x q=viν b z i j F H y a q := by
    unfold viν; rw [ d_cast h, hx _ _ ( List.Forall₂.cons ⟨rfl,congrQ.normal _⟩ h ), hv _ _ (List.Forall₂.cons ⟨rfl,congrQ.normal _⟩ he) ]; -- ambiguity he.M lens.
lemma pair_per (b A B K)(h: Speaks F)(hv:Speaks H): Speaks ( PairV b μ A B K F H ):= by intro x y hh; apply scatter_twins hh; intro i v w k hi hj; simp_rw [ eye b _ _ _ h hv _ _ _ _ hi hj, show be A (net i)=be A (net w) from φ_per _ (n_cast hi) ] -- eta lens
lemma detach_tw (h:Speaks F){x y:Lengths G}(hv:twins x y): detach P F x=detach P F y:= by unfold detach; simp_rw [show ∀ i j:Lane4 G,F (i::j::x)=F ( i::j::y ) from fun i j=> h _ _ (.cons ⟨rfl,congrQ.normal _⟩ ( .cons ⟨rfl,congrQ.normal _⟩ hv )) ]; -- erase
lemma detach_pin (h:SpeaksK P)(hx:Speaks F): pinQ ( detach P F x ):= fun {i j} he=> by unfold detach; simp_rw [h _ _ he, show ∀ a b,F ((a,i)::(b,i)::x)=F ((a,j)::(b,j)::x) from fun a b=> hx _ _ (.cons ⟨rfl,he⟩ (.cons ⟨rfl,he⟩ (asc _) )) ]
lemma birth_pin (h:SpeaksK P)(hv: Speaks F): Speaks ( birth P F ):= fun x y hP=> by unfold birth; rw [detach_tw hv hP]; exact congr_arg ((1/16:ℂ)*·) ( pin_root (detach_pin h hv) (n_cast hP))
lemma frameV (v:Cover)(μ:Measure QP): PairV false μ v v P F H= Cabin (embed v) P μ F H := rfl
lemma Θ_z (μ:Measure QP): Θ_pc false μ 0 P F=cycle P μ F:= by funext l; unfold Θ_pc cycle; simp_rw [ show ∀ t:QP,be 0 t=1 from fun _=>by simp [ be, show embed 0=0 from (by ext; simp [embed])], one_mul, at_trc ]; rfl
-- **ρcap** actual mesh continuous order extension.
def σcap (n:Side): Measure QP := ∑ i:Site n, ENNReal.ofReal (νt n) • Measure.dirac (Coord i)
lemma finite_s (n:Side) : IsFiniteMeasure (σcap n):= by
    constructor; unfold σcap; rw [Measure.finsetSum_apply]; simp only [Measure.smul_apply,Measure.dirac_apply, mem_univ, Set.indicator_of_mem,smul_eq_mul,Pi.one_apply,mul_one ]; exact lt_of_le_of_ne le_top (ENNReal.sum_ne_top.mpr (fun i hi=> by finiteness))
lemma siteI (n:Side)(F:QP→ℂ): (∫ q,F q∂ σcap n)=totalW F n:= by
    unfold σcap; rw [integral_finsetSum_measure]; · simp_rw [integral_smul_measure,ENNReal.toReal_ofReal (ν_pos n).le, integral_dirac, ← Finset.smul_sum ];
    exact fun i _=> (integrable_dirac (by finiteness)).smul_measure (by finiteness)
end YM.MS.Orbit
