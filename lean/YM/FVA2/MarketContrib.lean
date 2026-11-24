import YM.FVA2.PowersLip
import YM.FVA2.InvJet
/-!
# Convergence contribution through smoother jet certificates
 -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
namespace YM.FVA2.Prow
open Function Filter Set MeasureTheory PositionX
open Pert Pert.Position Maxwell Maxwell.Free PositionX.Bare.Shop PositionX.Jet
open PositionX.Ribbon PositionX.Detector Elegant Rail
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge} {F:Labels.Frames G} {d k:ℕ}{I:Type*}{l:Filter I}{t:I→ℝ}
   {X Y:I→Word (Bank F d)} {p: Word (Bank F d)} {K K':I→Word (Buffer F d)}{P:Word (Buffer F d)}
def Gold (l:Filter I)(t:I→ℝ)(X Y:I→Word (Bank F d))(p: Word (Bank F d)): Prop:= ∀ a:Pert.Position.Section F d, Prow.side l t ( fun i=> lookie F a ∘ X i ) ( fun i=> lookie F a ∘ Y i ) (lookie F a ∘ p)
variable (h:Rag l t)(hx:Gold l t X Y p)
namespace Gold
include h hx
lemma lens (T:Test k): side l t ( fun i=> expose F T ∘ X i ) (fun i=> expose F T ∘ Y i ) ( expose F T ∘ p ) := by intro n; exact Tandem.every h (fun i=> hx ⟨ k, baring F d ∘ i,T⟩ n )
lemma board (D:Detector F d): side l t (fun i=> D.read ∘ X i) (fun i=>D.read ∘ Y i) ( D.read ∘ p ):= fun i=> Tandem.every h (fun j=> lens h hx ( T:=(reachedV _ j).f ) i )
lemma reports (D:Detector F d)(hp:D.patch (p 0)) : side l t (fun i=>D.report ( X i )) (fun i=>D.report ( Y i )) (D.report p):= by exact side.runs h ( hx.board h D ) _ ( pick_nice hp )
lemma shop (hp:side l t K K' P): Gold l t (fun i=> predMarket ( K i ) ( X i )) (fun i=>predMarket ( K' i ) ( Y i )) ( predMarket P p ):= by intro s i; simp_rw [Function.comp_apply, Ribbon.all_tips _ _ (s:=s) i]; exact side.runs h ( side.pairS h ( hx.lens h s.f ) hp ) _ ( cross_smooth F s.p|>.contDiffAt ) i
lemma rebuy {a b:I→ Word ℝ}{p':Word ℝ}(hv:side l t a b p'): Gold l t (fun i=>ren ( a i ) ( X i )) (fun i=> ren ( b i ) ( Y i )) ( ren p' p ):= by intro a; simp_rw [ ren_writes ]; exact side.twistS h ( hx a ) hv
end Gold
variable {U V: I→Word ℝ} {Z:Word ℝ}
open PowerSeries
open MS.Book MS.Book.Convolve MS.Book.Program
open Clock Score Attend WorldJet
namespace Tandem
variable {A B C D:I→ℂ} {z c:ℂ}
include h
lemma alsoC (hp:Tandem l t A B z) (ht:Tandem l t C D c): Tandem l t ( A*C ) ( B*D ) ( z*c ):= ( hp.pairUp h ht ).after h (fun z=>z.1*z.2) (by fun_prop)
lemma alsoI (hp:Tandem l t A B z) (hj:z≠0): Tandem l t ( A⁻¹ ) ( B⁻¹ ) z⁻¹:= hp.after h (fun x=>x⁻¹) (by fun_prop)
lemma alsoP (hp:Tandem l t A B z)(j:ℕ): Tandem l t ( A^j ) ( B^j ) ( z^j ):= hp.after h (fun x=>x^j) (by fun_prop)
lemma minus (hp:Tandem l t A B z)(he:Tandem l t C D c): Tandem l t ( A-C ) ( B-D ) ( z-c ):= (hp.pairUp h he).after h (fun x=>x.1-x.2) (by fun_prop)
end Tandem
section inverse
include h
omit h in
private lemma hours {a:Word ℝ}(hh:Genuine a)(n:ℕ) : (Jet.inverse a n:ℂ)=( ( (a 1:ℝ):ℂ )^n)⁻¹ * ((headway n:ℂ) - ∑ i∈ Finset.range n,Program.cut (symbol a) i n * (Jet.inverse a i:ℂ) ):= by -- InvJet.Use
    have hp:= congr_arg Complex.ofReal (congr_fun ( headback hh ) n ); rw [renReal _ hh.1 n, Finset.sum_range_succ, ageT (litK hh.1), bill_q] at hp; rw [← hp]; field_simp [show ((a 1):ℂ)≠0 from by exact_mod_cast hh.2]; ring
variable (hZ:Prow.side l t U V Z)
include hZ
private lemma cutoff (i j:ℕ): Tandem l t (fun x=> Program.cut (symbol ( U x ) ) i j) (fun x=> Program.cut (symbol ( V x )) i j ) ( Program.cut (symbol Z) i j ):= by
    induction i generalizing j with
    | zero=> unfold Program.cut; simp only [pow_zero]; exact Tandem.stable h _ -- args
    | succ i ih=> unfold Program.cut; simp_rw [pow_succ,coeff_mul]; refine Tandem.sums h _ (fun i _=> Tandem.alsoC h ( ih i.1 ) ?_ ); simp_rw [bill_q]; exact Tandem.after h (hZ _) Complex.ofReal (Complex.ofRealCLM.contDiff.contDiffAt)
lemma side.inverted (hp: Genuine Z)(hu:∀ᶠ i in l,Genuine ( U i ) ∧ Genuine ( V i )): side l t ( inverse ∘ U ) (inverse ∘ V) ( inverse Z ):= by
    intro n; suffices H: Tandem l t ( fun i=> (( Jet.inverse ( U i ) n):ℂ) ) (fun i=>(( Jet.inverse ( V i ) n ):ℂ)) ( (Jet.inverse Z n):ℂ ) from H.after h _ Complex.reCLM.contDiff.contDiffAt ;
    induction n using Nat.strong_induction_on with
    | h n ih=>
       let f(a: Word ℝ)(p:Word ℝ):=( ( (a 1:ℝ):ℂ )^n)⁻¹ * ((headway n:ℂ) - ∑ i∈ Finset.range n,Program.cut (symbol a) i n * ( p i:ℂ) ); rw [ hours hp ]; obtain hh : Tandem l t ( fun x=> f ( U x ) ( Jet.inverse ( U x )) ) ( fun x=>f ( V x ) ( Jet.inverse ( V x ))) ( f Z ( Jet.inverse Z ) ):= Tandem.alsoC h ( Tandem.alsoI h ( Tandem.alsoP h (Tandem.after h (hZ 1) Complex.ofReal (Complex.ofRealCLM.contDiff.contDiffAt)) n ) (pow_ne_zero _ ( by exact_mod_cast hp.2 )) ) ( Tandem.minus h (Tandem.stable h (headway n:ℂ)) ( Tandem.sums h _ (fun i hi=> Tandem.alsoC h ( cutoff h hZ i n ) ( ih i (Finset.mem_range.mp hi) ) ) ));
       exact Tandem.reverse h (Tandem.congr (Tandem.reverse h ( Tandem.congr hh ( hu.mono (fun i hi=> ( hours hi.1 n ).symm )) )) ( hu.mono (fun i hi=> (hours hi.2 n).symm )))
end inverse
end YM.FVA2.Prow
