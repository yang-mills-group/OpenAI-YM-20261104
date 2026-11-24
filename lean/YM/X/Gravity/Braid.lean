import YM.X.Gravity.Oracle
/-!
# Norm independent power prices Q_φ unscaled and certified variation along released test directions.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Gravity
open Lattice Wilson Next.Rank Normal Interval PertExtension LatticePT Filter Set Function Metric MeasureTheory Asymptotics Reed Size Braid
open MvPolynomial Hinge Clove Haze Grow Shelf Ocean Fielding Crystal Perch LiftMark
open Stems hiding X
open scoped Topology ContDiff BigOperators Classical
variable {q: ℕ+}(hq:1<q.val){V:Type*}{k m n d l:ℕ}{G:Gauge}{R r:ℝ}
local notation "L"=>(atTop:Filter ℕ)
local notation "Ψ"=> Book G
local notation "e"=>epsilon q
variable (P:Word G)(φ:Floor R)
lemma still_sum (p:Curly G)(d:ℕ) : level (vapor G) d (bloom d p)=bloom d p:= by rw [few_commute (Y:=(valP (G:=G))) (E:=Okay G) (show d≤d from le_rfl)] -- explicit only
lemma sumsS (p:Book G) (h:level (vapor G) d p=p):∑ i∈Finset.range (d+1), leaf (vapor G) i p=p:= by rw [← trimmer]; exact h
section
include hq
lemma price_shrink : (fun i=> e i • exposed q P φ i)∈Badge Ψ (fun f => f∈ fades ℂ) ⊤:= by
   let w:=P.d; let p(i):= exposed q P φ i; let u(k i:ℕ): Book G:= e i • leaf (vapor G) k (p i); rw [show (fun i=>e i • exposed q P φ i)=∑ k∈Finset.range (w+1),u k from ?_]; apply Submodule.sum_mem; intro k hk; exact ordered (le_top) (fun f x=> x) (separator_lead hq P φ (by simpa using hk: k≤ w))
   ext1 i; rw [Finset.sum_apply]; unfold u; rw [← Finset.smul_sum]; exact Eq.symm (congr_arg (fun x:Book G=> e i • x) (sumsS (p i) (still_sum (warp q P φ i) w)))
end
-- normalized evaluate along moving jets
variable {x:Rich G}
lemma probe_generic (E : ℕ→Type*)[∀ i,NormedAddCommGroup (E i)][∀ i,NormedSpace ℝ (E i)] [∀ i,FiniteDimensional ℝ (E i)] (j: Kite E) (c:ℕ→ (i:ℕ)→E i) (h:∀i, Released (fun k=> c k i)): Released (fun k=> probeL (c k) (MvPolynomial.X j)):= by
    obtain ⟨t,h⟩:=h j.1; let C:= (owns E j.1).coord j.2; have he : Continuous ⇑C:= C.continuous_of_finiteDimensional; simp_rw [probeL,MvPolynomial.aeval_X]; exact ⟨↑(C t),Complex.continuous_ofReal.continuousAt.tendsto.comp (he.continuousAt.tendsto.comp h)⟩
set_option maxHeartbeats 600000 in
lemma probe_gr (h:Grasp x)(p:Book G): Released (fun i=> probeL (x i) p):= by
   induction p using MvPolynomial.induction_on with
   | C x=> simp only [probeL,aeval_C]; exact constell x
   | add p q x y=> simp only [map_add]; exact Released.add x y
   | mul_X p i IH=>
       simp only [map_mul]; have he:= probe_generic (Okay G) i x h; exact breaths IH he

lemma leased (h:Grasp x){f:ℕ→Book G}{H:Submodule ℂ (Book G)}(hf:f∈ Badge Ψ Released H): Released (fun i=> probeL (x i) (f i)):= by
   induction hf using Submodule.span_induction with
   | mem i he=> obtain ⟨c,b,hc,_,rfl⟩:= he; simp_rw [map_smul]; exact breaths hc (probe_gr h b)
   | zero=> simp only [Pi.zero_apply,map_zero]; exact Released.zero
   | add a b _ _ u t=> simp only [Pi.add_apply,map_add]; exact u.add t
   | smul a b _ t=> simp only [Pi.smul_apply,map_smul]; exact breaths (constell a) t
lemma unclog_eval (x:Long G)(p:Book G)(a:ℝ): probeL x (a • p)=a • probeL x p:= map_smul ((probeL x).toLinearMap.restrictScalars ℝ) a p
lemma watch_level (p:Book G)(i:ℕ): level (vapor G) i (watch G d p)=watch G d (level (vapor G) i p):= by
   simp_rw [trimmer,map_sum]; exact Finset.sum_congr rfl (fun i _=> leaf_watch d p)
include hq
lemma test_early (hp:Grasp x): Released (fun i=> e i ^(-(P.d:ℤ)) • (probeL (emerge q x i) (exposed q P φ i - watch G P.d (exposed q P φ i)))):= by
   let b:=exposed q P φ; let w:= P.d; let B(i k:ℕ):= probeL (x i) (e i ^((k:ℤ)-w) • oracle k (b i))
   have ht : Released (fun i=> ∑ k∈Finset.range (w+1), B i k):= Released.sumR _ (fun i hi=> (leased hp (or_clamp hq P φ (by simpa using hi : i≤w))))
   have hh(i): level (vapor G) w (b i-watch G w (b i))= b i-watch G w (b i):= by rw [map_sub,watch_level,show level (vapor G) w (b i)=b i from still_sum ..]
   refine Eq.mp (congr_arg Released ?_) ht; ext1 i; -- left to right
   change _= _ • probeL _ (b i-watch G w (b i)); nth_rw 1 [← sumsS _ (hh i)]; rw [map_sum,Finset.smul_sum]; apply Finset.sum_congr rfl; intro k hk; unfold B; rw [unclog_eval, rise₀]; change _= _ • probeL (sauce (e i) (x i)) _; rw [dinner,smul_smul,zpow_sub₀ (epsilon_pos q i).ne',div_eq_mul_inv,zpow_neg,zpow_natCast,mul_comm];rfl
end YM.PositionX.Gravity
