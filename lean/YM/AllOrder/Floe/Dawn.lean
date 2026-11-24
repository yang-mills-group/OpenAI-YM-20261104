import YM.AllOrder.Floe.Slide
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Floe
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial
open Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G: Gauge} {c f n : Side} {k j w N : ℕ} {S:StepData c f}
variable {σ C Z D β Θ:ℝ}
open Module PertExtension GaussianScore
variable {Y X:Type} [NormedAddCommGroup X][NormedSpace ℝ X] [NormedAddCommGroup Y][NormedSpace ℝ Y]
variable [FiniteDimensional ℝ X][FiniteDimensional ℝ Y] (A: Law Y) {ι:Type}[Fintype ι](P:Basis ι ℝ Y)
    [MeasurableSpace Y][BorelSpace Y](μ:Measure Y) [μ.IsAddHaarMeasure] {u v:Book (X×Y)} (hu:u 0=0)(hv:v 0=0)
local notation "Ω"=>X×Y
local notation "r"=>arrowR A μ u
local notation "r'"=>arrowR A μ v
variable (hx:∀ n,Rank (X×Y) (n+2) (u n))(hz:∀ n,Rank (X×Y) (n+2) (v n))
local notation "X₀"=> ((0:ℕ))
include P hu hv hx hz
lemma proviso (he:∀ j<k, u j=v j) (hk:j<k) :∃ (R:Book (X×Y)),r j=R∧r' j=R:= by
 refine ⟨r j,rfl,?_⟩; suffices hh:∀ j<k,∀ s,r' j s=r j s from funext (hh j hk); intro i hi s; induction s using Nat.strong_induction_on generalizing i with
 | h s ih=>
    let h₀:Clear u:= fun n=> (hx n).read; let h₀':Clear v:=fun n=> (hz n).read
    rcases s with _|s; · rw [Fire.initial A μ hv h₀', Fire.initial A μ hu h₀,he i hi]
    rcases s with _|s; · rw [Fire.once A P μ hv h₀',Fire.once A P μ hu h₀];
    rw [stepping A P μ hu h₀,stepping A P μ hv h₀', ih s (by omega) i hi]
    apply congr_arg; apply congr_arg (·+_); apply Finset.sum_congr rfl; intro l hl; apply Finset.sum_congr rfl; intro j hj; rw [ih j (by have hh:= mem_range.mp hj; omega) l (by have hh:= mem_range.mp hl; omega),ih (s-j) (by omega) (i-l) (by omega)]
omit hu hv hx hz
lemma infinity_d (f g:Ω→ℝ)(hf:Plausible f)(hg:Plausible g): infinity A P f - infinity A P g= infinity A P (f-g):= by
 let d:=@diff' Ω _ _; have h (x:Ω) f g (hf:Plausible f)(hg:Plausible g): d x (f-g)=d x f-d x g:=funext fun i=>by unfold d diff'; rw [fderiv_sub (hf.smooth.differentiable (by simp) i) (hg.smooth.differentiable (by simp) i)]; rfl
 rw [infinity,infinity,infinity,←sum_sub_distrib]; apply Finset.sum_congr rfl; intro i _; rw [show diff' _ (f-g)=_ from h _ _ _ hf hg]; exact (h _ _ _ (hf.ds _) (hg.ds _)).symm
lemma cobill {f:Ω→ℝ} (h:Rank Ω N f): Rank Ω (N-2) (infinity A P f):= by
 rw [show N-2=N-1-1 by omega]; exact Rank.sum (fun i _=> (h.der _).der _)
-- Estimate SAME grade different books. Compare whole Hess model difference until mesh.Root. At positive grade interactions from strictly earlier pieces are identical if sources equal at those grades, so difference propagated through PURE Laplacian only.No new hull call. Price.
variable (m:ℕ)(hm:∀ j<k, u j=v j)(hk:1≤k)(h0: Rank (X×Y) N (u k-v k))
omit P
include hu
lemma rzero : r 0 m=0:= by unfold arrowR Fire.Warm; rw [fades (funext fun i=> fix0 A μ hu i)]; change beam (fun _: ℝ×Ω=>0) m=(fun _=>0); funext i; exact ((Act.static (n:=m) (0:ℝ)).writes _ le_rfl).trans (by simp [just])
omit [MeasurableSpace Y] [BorelSpace Y] [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] hu in
lemma j_zero (f:X→ℝ) (j:ℕ): jet (fun _:X=> (0:ℝ)) j=0 := by ext1 i; simp [jet]
omit hu
include P
omit [MeasurableSpace Y] [BorelSpace Y] in
lemma conn_left (f:Ω→ℝ): connection A P 0 f=0 ∧ connection A P f 0=0:= by
 have hh (x:Ω): diff' x (fun _=> (0:ℝ))=(fun _=>0):=funext fun i=>by unfold diff'; rw [fderiv_fun_const]; rfl
 constructor<;> apply Finset.sum_eq_zero <;> intro i hi
 · change diff' _ (fun _=>0)*_=0; rw [hh];exact zero_mul _
 change _*diff' _ (fun _=>0)=0; rw [hh];exact mul_zero _
include P hu hv hx hz hm hk
lemma stairs (m:ℕ): r k (m+2)-r' k (m+2)=(↑(m+2:ℕ):ℝ)⁻¹ • infinity A P (r k m -r' k m):= by
 rw [stepping A P μ hu (fun i=>(hx i).read),stepping A P μ hv (fun i=>(hz i).read)]
 let L i j:= connection A P (r i j) (r (k-i) (m-j)); let L' i j:=connection A P (r' i j) (r' (k-i) (m-j))
 have ht : ∑ i∈range (k+1), ∑ j∈range (m+1), L i j=∑ i∈range (k+1),∑ j∈range (m+1), L' i j:= by
    apply Finset.sum_congr rfl; intro i hi; apply Finset.sum_congr rfl; intro j hj; unfold L L'; by_cases h:i=k; rw [h,Nat.sub_self,rzero A μ hu _,rzero A μ hv _, (conn_left A P _).2,(conn_left A P _).2]; by_cases h₀:i=0; rw [h₀,rzero A μ hu _,rzero A μ hv _, (conn_left A P _).1,(conn_left A P _).1]; -- layout
    obtain ⟨t,hU,hW⟩:= proviso A P μ hu hv hx hz hm (j:=i) (by have hh:=mem_range.mp hi; omega); obtain ⟨v,hV,hZ⟩:= proviso A P μ hu hv hx hz hm (j:=k-i) (by omega); rw [hU,hV,hW,hZ]
 rw [← smul_sub]; refine congr_arg _ ?_; rw [← show infinity A P (arrowR A μ u k m)-_= _ from infinity_d A P _ _ ((high_rank A P μ hu hx m k).read) ((high_rank A P μ hv hz m k).read), ht]; abel
include h0
lemma children (m:ℕ): Rank (X×Y) N (r k m-r' k m):= by
 induction m using Nat.strong_induction_on with
 | h m ih=>
    rcases m with _|m; · rw [Fire.initial A μ hu fun i=> (hx i).read,Fire.initial A μ hv fun i=>(hz i).read]; exact h0
    rcases m with _|m; · rw [Fire.once A P μ hu fun i=> (hx i).read,Fire.once A P μ hv fun i=> (hz i).read,sub_zero]; exact Rank.nil N 0
    rw [stairs A P μ hu hv hx hz hm hk]; exact ((cobill A P (ih m (by omega))).up (by omega)).scal _
lemma unbent : Rank (X×Y) (N-2) ((booked A μ u k-booked A μ v k)-(u k-v k)):= by
 let f m:= r k m-r' k m; have he(i:ℕ) : Rank Ω (N-2) (f (i+1)):= by
    rcases i with _|i; unfold f; rw [Fire.once A P μ hu fun i=>(hx i).read,Fire.once A P μ hv fun i=>(hz i).read,sub_self]; exact Rank.nil _ 0;
    unfold f; rw [stairs A P μ hu hv hx hz hm hk]; exact (cobill A P (children A P μ hu hv hx hz hm hk h0 i)).scal _
 unfold Fire.booked; rw [←sum_sub_distrib, Finset.sum_range_succ', Fire.initial A μ hu fun i=>(hx i).read,Fire.initial A μ hv fun i=>(hz i).read,add_sub_cancel_right]; exact Rank.sum fun i _=> he i
end YM.AllOrder.Floe
