import YM.Qlocal.Canopy.Marque
import YM.Qlocal.Canopy.Roller
/-!
 # Stability of Auxiliary Analytics under crop of marked exponent entries
 When clipped analytic letter has a *factorizably tiny* held-interaction
 error, still SOP in polynomial Lane (after recovering a large cost
 due to exponent coupons on the paths), propagate with exactly the same
 nominal estimator and tolerance. Rank v = valuation under negative power shift,
 not tuple arity.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Bind
open Function Filter Set Metric Lattice MeasureTheory ProbabilityTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis Bid
open AllOrder Ker Laplace Laplace.SigmaP Response Catch Catch.Clock
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open Marker Multi PertExtension.Series Radial Extra.Iteration Floe PositionX.Jet
open Comparison.RG02.Order
open Comparison.RG02.Assembly
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G:Gauge} {k j i q r:ℕ} {n c f :Side}{S:StepData c f} {b α t:ℝ}
namespace Flute
variable {R K:reed G n} (he:Flute R k)(hp:Flute K k)
include he
lemma scaled (a:ℝ): Flute (a • R) k:= by
 constructor
 · intro s i V; simp only [Pi.smul_apply]; rw [he.byfield s i V]
 · exact fun s=> Envelope.mul (Envelope.const a) (he.envelope s)
 exact GradeAt.linear_contact (L:=(a • ContinuousLinearMap.id ℝ ℝ)) he.zeroAt
include hp
lemma add: Flute (R+K) k:= by
 constructor
 · intro s i V; simp only [Pi.add_apply]; rw [he.byfield s i V,hp.byfield s i V]
 · exact fun s=> (he.envelope s).add (hp.envelope s)
 exact he.zeroAt.add hp.zeroAt
omit he hp
lemma nil (k:ℕ): Flute (0:reed G n) k:= ⟨fun _ _ _=>rfl,fun _=> Envelope.const 0, GradeAt.grade_zero _⟩
end Flute
namespace Horn
variable {ι σ:Type*}{T: Catch.Clock ι}{P:Patch}{K:KernelChoices}{v:Stage}{u:ℝ→ℝ}{κ:ℕ}{F:Uniform.Before G v.width v.paths P.J K (k+3)}
variable {R:ι → Aux.Name G P K u κ v k F}
abbrev ListV (R:ι → Aux.Name G P K u κ v k F):= (i:ι)→ reed G (R i).f
namespace Lane
variable {A B:ListV R} (hA:Lane R A T j q) (hB:Lane R B T j r) (h: Lane R B T j q)
set_option quotPrecheck false
local notation "X[" i "]"=> (R i).X
local notation "Z"=>fun i:ι=> ℝ×(X[i] × Poll.Body (R i).Vx)
local notation "uℓ"=> Set.univ
set_option quotPrecheck false
local notation "S"=>T.book (V:=Z) (fun _=> ball 0 1)
local notation "y"=> fun i:Σ i:ι,{x:Z i//x∈ball 0 1}=> i.2.1
local notation "C[" i "]" => Config G (R i).f
local notation "S0"=>T.book (V:=fun i=>C[i]) (fun i=>{x | flags (R i).price.threshold x=∅})
abbrev stamp (A:ListV R)(i:ι):= song (R i) (A i)
local notation "R₀" => fun i=> (R i).Θ
-- Finite product/selection at ALL germs and all real witnesses. specialize later.
abbrev Night (A:ListV R)(j:ℕ) := Catch.Cover (V:=fun i=> Z i.1) S j 0 (fun _=>1) (fun i=> stamp A i.1) y -- S notation references T shadow.Bug
abbrev Blank (A:ListV R): Prop:=(S0).Meter (fun i=> A i.1 (R i.1|>.Θ) i.2.1) 0
lemma gigs (hp:∀ i,Flute (A i) q)(hx:Night (T:=T) A j)(hv:Blank (T:=T) A): Lane R A T j q:= by
 refine ⟨hp,?_,?_⟩
 · intro e he; filter_upwards [show ∀ᶠ i in T.rail,∀ x∈ Metric.ball (0:Z i) 1, Brush j (T.cost i ^e) 1 (stamp A i) x from (T.booked _ _).mp (hx e he)] with i hi z hz using hi z (mem_ball_zero_iff.mpr hz)
 exact fun p hp=> (T.booked _ (fun i (x:C[i])=> |A i (R i).Θ x| ≤ T.cost i^p)).mp (hv p hp)
include hA
lemma nights : Night (T:=T) A j:= Catch.Cover.book_home (p:=fun _=>1) (fun _=> Metric.ball (0:Z _) 1) (f:=stamp A) (fun p hp=> Eventually.mono (hA.militia p hp) (fun i hi z hz=> hi z (mem_ball_zero_iff.mp hz)))
lemma blanch : Blank (T:=T) A:= fun p hp=> (T.booked _ _).mpr (hA.allReal p hp)
lemma chosen (c:ι→ℝ)(hc:T.Meter c 0): Lane R (fun i=> c i • A i) T j q:= by
 refine gigs (fun i=> (hA.tells i).scaled _) (Cover.weak (X:=Σ i:ι,{x:Z i//x∈ball 0 1}) (Cover.smul hA.nights (hc.pays Sigma.fst (T.liftF _))) (by norm_num)) (((hc.pays Sigma.fst (T.liftF _)).mul hA.blanch).weak (by norm_num)) -- defeq layering failure
include h in
lemma summons : Lane R (A+B) T j q:= gigs (fun i=> (hA.tells i).add (h.tells i)) (hA.nights.add h.nights) (hA.blanch.add h.blanch)
include hB
lemma produce : Lane R (A*B) T j (q+r):= gigs (fun i=> (hA.tells i).pair (hB.tells i)) ((hA.nights.mul hB.nights).weak (by simp)) ((hA.blanch.mul hB.blanch).weak (by simp))
omit hA hB
lemma nil : Lane R 0 T j q:= by
 refine gigs (fun i=> Flute.nil q) (Cover.fixed (X:=Σ i:ι,{x:Z i//x∈ball 0 1}) (fun _=> (0:ℝ)) (Eventually.of_forall fun _=>zero_le_one) (?_)) (Clock.Meter.nil _ _)
 simp_rw [norm_zero]; exact Clock.Meter.nil _ _
lemma one : Lane R 1 T j 0:= by
 refine gigs (fun i=> Flute.one) ?_ (Meter.const S0 1); exact Cover.fixed (c:=fun _=> (1:ℝ)) (Eventually.of_forall fun _=>zero_le_one) (Meter.const S ‖(1:ℝ)‖)
end Lane
variable (K':ι→ℝ) (H F':σ→ ListV R)(w:σ→ℕ)
-- clipping certificate.T.Use separately at input marks & output offprop.Lanes read for each clip.Exact Θ Support.True.
def Shrunk (T:Catch.Clock ι)(j q:ℕ)(K':ι→ℝ) (A B:ListV R) := Lane R A T j q ∧ ∃ Δ:ListV R,Lane R Δ T j q ∧ B= fun i=> A i+ K' i • Δ i
namespace Shrunk
variable {K'} {A B L M:ListV R}
local notation "ξ"=>fun P:Finset σ=> fun i=> Flute.bill (fun j=>(H j) i) P
noncomputable abbrev object (H:σ→ ListV R)(P:Finset σ): ListV R:= (fun i=> Flute.bill (fun j=>(H j) i) P)
lemma things (P:Finset σ): object H P= ∏ i∈P,H i:= by unfold object Flute.bill; funext x; rw [Finset.prod_apply]
variable (hc: T.Meter K' 0)
include hc
lemma bar (h:Shrunk T j q K' A B): Lane R B T j q:= by obtain ⟨ht,u,hh,rfl⟩:=h; exact ht.summons (hh.chosen K' hc)
lemma prod (h:Shrunk T j q K' A B)(h':Shrunk T j r K' L M): Shrunk T j (q+r) K' (A*L) (B*M):= by
 let hh:=bar hc h'; obtain ⟨h,B',hB,hx⟩:=h; obtain ⟨h',L',hV,hl⟩:=h'; refine ⟨h.produce h', B'*M+A*L', (hB.produce hh).summons (h.produce hV),?_⟩; ext i x y; simp only [hx,hl,Pi.mul_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul]; ring
lemma collective (P:Finset σ)(he:∀ i∈P,Shrunk T j (w i) K' (H i) (F' i)): Shrunk T j (Flute.size w P) K' (object H P) (object F' P):= by
 simp_rw [things,Flute.size]; induction P using Finset.induction_on with
 | empty=> rw [Finset.prod_empty,Finset.prod_empty, Finset.sum_empty]; refine ⟨Lane.one,(0:ListV R),?_,?_⟩; · exact Lane.nil -- k implicit bug.
           ext; simp
 | insert i p hi ih=> rw [Finset.prod_insert hi,Finset.prod_insert hi,Finset.sum_insert hi]; exact Shrunk.prod hc (he _ (mem_insert_self ..)) (ih (fun i hi=>he i (mem_insert_of_mem hi)))
end Shrunk
end Horn
end YM.Qlocal.Bind
