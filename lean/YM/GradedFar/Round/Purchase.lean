import YM.GradedFar.Round.Crew
import YM.GradedFar.Round.Sign

/-!
# Estimates on the rounded compact-audit set
-/
namespace YM.FVA2.GradedFar.Physical.Round
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh
open Moving Growth Pose Books Scale Dframe Jury Facets
open Continuation Continuation.Window
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {n m h t p : ℕ} {I J:Type} {d : Fin n → ℕ}{e: Fin m→ℕ} (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {simple : G.Simple} {A : MS.Land.Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
local notation "τ"=>𝓝[>] (0:ℝ)
local notation "g"=>gYM G
local notation "ν"=> Teller.logNu 1
local notation "α"=> Measure.adjust N.scheme N.criterion
include H
variable {K:Set (Points n)}{S:Set (Points m)}(hK:IsCompact K)(hk:K⊆conf n)(hS:IsCompact S)(hs:S⊆ Outside m)
include hK hk hS hs
lemma before_revenue (a:Tags G h (n+m))(p:ℕ) : Rain 0 (fun (i:XSet K S)(s:ℝ)=> coeff p (Pose.line N (flute i s) a)) := by
    have ht : actMark (mirror (α h)) (book N h) = Pose.Bbook N h := by
      change actMark (mirror _) (actMark (α h) (Pose.Bbook N h)) = _; rw [acts, (recruited_j N M H).turn', acts_h]
    unfold Pose.line; simp_rw [coeff_mk,← ht,fxt_m,seen]
    apply Rain.sum; intro i _; -- transfer via ranker
    have hb:= revenue N M H hK hk hS hs (pulseU i (mirror (α h)) a) (i none); unfold ranker boundary shop Reg.Point.story at hb; simp_rw [coeff_mk] at hb; exact hb

variable (b:Board I) (r : I→ℝ)
local notation "L"=>gYM G ∘ r
variable (hr:Tendsto r b.l (𝓝[>] (0:ℝ))) (hb:b.g=gYM G∘r)
local notation "x"=>b.s
local notation "T"=>b.l
omit H hK hk hS hs in
lemma enroll {E:Type}[NormedAddCommGroup E]{u:I→E} (h:Buys T u b.g p) : Bill b p 0 u:= by
   obtain ⟨C,hC,h⟩:=h.exists_pos; refine ⟨C,hC,0,?_⟩; filter_upwards [h.bound,b.positive] with i hi hp
   rw [post,pow_zero,neg_zero,zero_mul,exp_zero,mul_one,mul_one]; rwa [Real.norm_of_nonneg (by positivity)] at hi

omit H hK hk hS hs in
private lemma combo_price (k:ℕ) (D':I→ Normalize.Change G h)(a:Tags G h n)(j:Choices G (fun _:Fin n=>h))
   (hD:Buys T (fun i=>guide G h (D' i)) b.g k): Bill b k 0 (fun i=> combo (stand (D' i)∘a) j - combo a j) := by
      apply enroll b; -- lift scalar costs
      suffices H:∀ s:Finset (Fin n), Buys T (fun i=>(∏ l∈s,coord (j l) (stand (D' i) (a l))) - (∏ l∈s,coord (j l) (a l))) b.g k from H Finset.univ
      intro s; induction s using Finset.induction_on with
      | empty=> simp_rw [Finset.prod_empty,sub_self]; exact isBigO_zero ..
      | insert i s h ih=>
         let t l:= coord (j i) (stand (D' l) (a i)); let t':= coord (j i) (a i)
         have hx:= coord_change (a i) (j i) hD; have hv: Buys T t b.g 0:= by simpa only [t,t',sub_add_cancel] using (budget_growth T (p:=k) hx 0 (Nat.zero_le _) (jet_level T b.shrinking)).add (budget T (C:= ‖t'‖) (q:=fun _=>t') («g»:=b.g) (Eventually.of_forall fun _=> le_rfl))
         have hn:= times_cost T hv ih; let X :=∏ l∈s,coord (j l) (a l); rw [zero_add] at hn
         simp_rw [Finset.prod_insert h]; refine (hn.add (times_cost T hx (budget T (C:= ‖X‖) (q:=fun _=>X) («g»:=b.g) (Eventually.of_forall fun _=> le_rfl)))).congr_left (fun l=>?_)
         unfold t X; ring
omit H hK hk hS hs in
private lemma time_leap (u t':I→ℝ)(he':∀ᶠ i in T,|u i|≤2*b.g i)(hv:∀ᶠ i in T,|t' i|≤2*b.g i)
    (he:Buys T (fun i=>(u i:ℂ) - (t' i:ℂ)) b.g (p+1))(j:ℕ) : Bill b (p+1) 0 (fun i=> (u i:ℂ)^j - (t' i:ℂ)^j):= by
      induction j with| zero=>simp_rw [pow_zero,sub_self]; exact Bill.from_zero _| succ j ih=>
        let t i:ℂ:=u i; let v i:ℂ:=t' i
        have hp:Bill b 0 0 t :=by simpa only [pow_one] using ((Ledger.exponent he' 1).mono_fee (v:=0) le_rfl zero_le_one)
        have ht:= (Ledger.exponent hv j).mono_fee (v:=0) le_rfl j.zero_le
        have h0:=ih.earns hp; have h2:=(enroll b he).earns ht; rw [zero_add] at h0 h2
        exact (h0.plus h2).apply_eq (Eventually.of_forall fun i=> by unfold t; rw [pow_succ,pow_succ]; ring)
omit H hK hk hS hs in
private lemma leap (u t':I→ℝ) (he':∀ᶠ i in T,|u i|≤2*b.g i) (hv:∀ᶠ i in T,|t' i|≤2*b.g i)
   (he:Buys T (fun i=>(u i:ℂ) - (t' i:ℂ)) b.g (p+1))(F:I→PowerSeries ℂ)(hF:Ledger b p 0 F) : Bill b (p+1) 0 (fun i=>crop p (u i) (F i)-crop p (t' i) (F i)) := by
      simp only [crop_eq]; simp_rw [← Finset.sum_sub_distrib,← sub_mul]; apply Bill.sum; intro j hj; simpa only [zero_add] using (time_leap b u t' he' hv he j).earns (hF j (Finset.mem_range_succ_iff.mp hj))
private lemma tick {k q:ℕ}(t':I→ℝ)(hv:∀ᶠ i in T,|t' i|≤2*b.g i)(a:Tags G h (n+m))(D':I→Normalize.Change G h)
    (hD:Buys T (fun i=>guide G h (D' i)) b.g k) (P:I→XSet K S) : Bill b k 0 (fun i=> crop q (t' i) (Pose.line N (flute (P i) (b.s i)) (stand (D' i)∘a))-crop q (t' i) (Pose.line N (flute (P i) (b.s i)) a)) := by
   let Φ i:= stand (D' i)∘a
   have hy a:Ledger b q 0 (fun i=>Pose.line N (flute (P i) (b.s i)) (a:Tags G h (n+m))) :=fun i _=> Bill.of_rain (before_revenue N M H hK hk hS hs a i) P
   have hA: Bill b k 0 (fun i=> crop q (t' i) (Pose.line N (flute (P i) (b.s i)) (Φ i))-crop q (t' i) (Pose.line N (flute (P i) (b.s i)) a)) := by
      let E (j:Choices G (fun _:Fin (n+m)=>h)) i:= (combo (Φ i) j-combo a j)*crop q (t' i) (Pose.line N (flute (P i) (b.s i)) (basisInputs j))
      have he j : Bill b k 0 (E j):= by simpa only [zero_add] using (combo_price b k D' a j hD).earns ((hy _).evaluate hv)
      apply (Bill.sum _ (fun i (_:i∈Finset.univ)=> he i)).apply_eq (Eventually.of_forall _); intro i
      rw [Pose.roman N (Φ i),Pose.roman N a]; unfold E; simp_rw [sub_mul,Finset.sum_sub_distrib]
   exact hA

include hb hr
lemma before_sale (k q:ℕ)(hp:p≤q)(hp':p+1≤k) (Y:I→ Tags G h (n+m) →ℂ)
    (t':I→ℝ) (D':I→Normalize.Change G h)(ht:Tendsto (fun i=> t' i / L i) T (𝓝 1)) (u:I→ℝ) (he':∀ᶠ i in T, |u i|≤ 2* L i) (he:Buys T (fun i=>(u i:ℂ) - (t' i:ℂ)) L (p+1))
    (hD: Buys T (fun i=>guide G h (D' i)) L k) (a:Tags G h (n+m)) (P:I→XSet K S) (H0:Buys T (fun i=> Y i a - crop q (t' i) (Pose.line N (flute (P i) (b.s i)) (stand (D' i)∘a))) L k) :
    Priced b p u 0 (fun i=>Y i a) (fun i=>Pose.line N (flute (P i) (b.s i)) a) := by
   have hv:∀ᶠ i in T,|t' i|≤2*b.g i := ((sailed N M H T r hr ht).mono (fun i h=> by rw [hb]; exact h.2)); rw [←hb] at hD H0 he he' ht
   let Φ i:= stand (D' i)∘a
   have hy a:Ledger b q 0 (fun i=>Pose.line N (flute (P i) (b.s i)) (a:Tags G h (n+m))) :=fun i _=> Bill.of_rain (before_revenue N M H hK hk hS hs a i) P
   let F i:=Pose.line N (flute (P i) (b.s i)) a
   have hA: Bill b k 0 (fun i=> crop q (t' i) (Pose.line N (flute (P i) (b.s i)) (Φ i))-crop q (t' i) (Pose.line N (flute (P i) (b.s i)) a)) := tick N M H hK hk hS hs b t' hv a D' hD P
   have htons:= leap b u t' he' hv he F ((hy a).monotone hp)
   refine ⟨(hy a).monotone hp,?_⟩; exact (((((enroll b H0).plus hA).mono_fee le_rfl hp').minus htons).plus ((hy a).below hv hp)).apply_eq (Eventually.of_forall fun i=> by unfold Φ F; abel)
end
end YM.FVA2.GradedFar.Physical.Round
