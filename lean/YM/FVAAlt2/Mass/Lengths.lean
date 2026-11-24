import YM.FVAAlt2.Mass.Packet
/-! # Log-power budgets on scaled physical separated moments -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.FVA.Currency
open Set Function Filter Finset Metric MeasureTheory Real
open Plane Koszul Landau Detect Heat Tone Latch Latch.Job Rake Orbit Breeze Book Convolve Flux Osc Snap City Job Geo Land Local.Physical Port Tide Vista Vane Fleet Dial
open _root_.YM.FVAAlt2.Home.Profiles
open _root_.YM.MS.Theater
open Puff Mom Puff.Actors
open scoped Topology ContDiff Classical
variable {G:Gauge}{B:Deck G}{M:Land.Booked B} {n j k m:ℕ}{K:Set (Points n)}{x:ℝ}
local notation "I"=> Shelf K
local notation "Q"=> Fin n
local notation "V"=> Finset Q
variable (T:Fin n→ℕ)
local notation "ψ"=> Trunk.stack ( SplitP.marked (Fin n) )
namespace LowW
variable {f f':Shelf K→ℂ}
lemma constant (c:ℂ): LowW x (K:=K) (fun _=>c):= ⟨‖c‖,norm_nonneg _,0,fun i=> by simp⟩
lemma added(h:LowW x f)(h':LowW x f'): LowW x (f+f'):=by obtain ⟨a,ha,k,hf⟩:=h; obtain ⟨b,hb,l,hb'⟩:= h'; refine ⟨a+b,by linarith,k+l,fun i=>?_⟩; let y:ℝ:=1+|x+i.scale|; have hy:1 ≤ y:= le_add_of_nonneg_right (abs_nonneg _); apply ( norm_add_le _ _ ).trans; apply (add_le_add ( hf i ) (hb' i)).trans; rw [add_mul]; gcongr  <;> omega
lemma product(h:LowW x f)(h':LowW x f'): LowW x (f*f'):=by obtain ⟨a,ha,k,hf⟩:=h; obtain ⟨b,hb,l,hb'⟩:=h'; refine ⟨a*b,mul_nonneg ha hb,k+l,fun i=>?_⟩; rw [Pi.mul_apply,norm_mul]; exact (mul_le_mul (hf i) (hb' i) (norm_nonneg _) (by positivity)).trans_eq (by rw [pow_add]; ring)
lemma sums {S:Type*}(q:Finset S)(f:S→Shelf K→ℂ)(h:∀ i∈q,LowW x (f i)): LowW x ( fun z=>∑ i∈q,f i z ):= by induction q using Finset.induction_on with| empty=> simpa using constant (0:ℂ)| insert i s H ih=> simp_rw [Finset.sum_insert H]; exact (h i (by simp)).added ( ih (fun j hj=> h j (mem_insert_of_mem hj )))
end LowW
def Hour (f:Shelf K→ Finset (Fin n)→ℕ→ℂ)(μ:ℝ)(T:Fin n→ℕ): Prop:= ∀ j k, LowW μ (fun x:Shelf K=> moving (Vane.charge T j) x.scale • f x j k)
variable {g f:Shelf K→ Finset (Fin n)→ℕ→ℂ}{μ:ℝ}
lemma jointGreen (h:Hour f μ T)(g': Hour g μ T): Hour (fun i=> (ψ).core ( f i ) ( g i )) μ T:= by
 intro j k; let σ(i:I):= (ψ).core (f i) (g i); let w:= Vane.charge T; let S:= SplitP.subs j; let N:=antidiagonal k; have he(s:Finset (Fin n)×Finset (Fin n))(hs:s∈S)(t:ℝ): moving (w j) t=moving (w s.1) t*moving ( w s.2 ) t:= by
    obtain ⟨ a,b⟩:= SplitP.joins.mp (show (s.1,s.2)∈SplitP.subs j from hs); unfold w moving Vane.charge; rw [← a,Finset.sum_union b,pow_add ]
 change LowW _ ( fun i=> _ • σ i j k ); simp_rw [ σ, show ∀ i:I,(ψ).core ( f i ) (g i) j k= (∑ s∈S, Trunk.core (f i s.1) (g i s.2)) k from fun i=> rfl, Finset.sum_apply, Finset.smul_sum ]; apply LowW.sums; intro i hi; change LowW μ (fun v:I=> moving _ _ • (∑ s∈ N, f v i.1 s.1*g v i.2 s.2));
 simp_rw [Finset.smul_sum]; refine LowW.sums _ _ (fun s hs=>?_ ); change LowW μ (fun v:I=> moving ( w j ) v.scale • _); simp_rw [he i hi,Complex.real_smul,Complex.ofReal_mul, mul_mul_mul_comm ]; exact LowW.product ( f:=fun v:I=> (↑(moving _ _):ℂ) * f v i.1 s.1 ) ( h i.1 s.1 ) (g' i.2 s.2)
lemma powGreen (v: Hour f μ T)(i:ℕ) : Hour (fun j=> (ψ).power (f j) i) μ T:= by
 induction i with
 | zero=> intro j k; unfold Actors.power Actors.stack SplitP.refineV; by_cases he:j= (SplitP.marked Q).origin; · have hx : j=∅:=he; simp_rw [if_pos he,hx]; unfold moving Vane.charge; simp only [Finset.sum_empty,pow_zero,one_smul]; exact LowW.constant _
          simp_rw [if_neg he]; simp only [Pi.zero_apply,smul_zero]; exact LowW.constant _
 | succ i ih=> exact jointGreen _ v ih
lemma onHour (v: Hour f μ T) : Hour (fun j=>bouquet (f j)) μ T:= by intro j k; simp_rw [bouquet,Cheer,Actors.cheers, Finset.sum_apply, Finset.smul_sum]; refine LowW.sums _ _ fun i _=>?_ ; simp only [Actors.wages,Pi.smul_apply, smul_comm (moving _ _) ]; exact ( LowW.constant (_:ℂ) ).product ( powGreen _ v i _ _ )
variable (A: MS_Data G M)(x:ℝ) (p:Fin n→ Label B)
lemma sizedA (hK:IsCompact K) (h:K ⊆ conf n) : Hour (K:=K) (fun i: Shelf K=> tour A p x (exp i.scale • realize i.pose)) x (Rake.Label.h ∘ p):= onHour _ (cumulants A x p hK h)
end YM.MS.FVA.Currency
