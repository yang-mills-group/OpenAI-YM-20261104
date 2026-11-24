import YM.X.Reed.Brook
/-!
The lift chooses tower through moments. Uniform labor. Scaled highest term convergence.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Reed
open Lattice Wilson Stems Next.Rank.CellsInt Next.Rank.Beamer Tensor TensorProduct Filter MeasureTheory Metric Finset Function Maxwell Asymptotics
open scoped Topology ContDiff BigOperators
variable {G:Gauge} {V:Type*} [NormedAddCommGroup V][NormedSpace ℝ V] {n k m:ℕ}
variable {R:ℕ→ℕ}{C e:ℕ→ℝ}{A:ℕ→Brush G}
local notation "Fℕ"=>(atTop:Filter ℕ)
abbrev Long (G:Gauge):= (n:ℕ)→Okay G n
def arm (n:ℕ): Long G→ₗ[ℝ] Brush G:= ∑ i∈range n, valP i ∘ₗ LinearMap.proj i -- length n
lemma arm_point (n:ℕ)(p:Long G): arm n p= ∑ i∈range n, launch (p i):= by rw [arm,LinearMap.sum_apply];rfl
lemma arm_succ (n:ℕ)(p:Long G): arm (n+1) p=arm n p+launch (p n):= by rw [arm_point,arm_point,sum_range_succ]
lemma Bark.arm_sub {l:ℕ}(h:Bark R C l m A)(p:ℕ→Long G)(hl:n≤l): Bark R C l m (fun k=> A k-arm n (p k)):= by
    intro j L; refine (h j L).move (Eventually.of_forall ?_); intro k; dsimp only; rw [arm_point]; simp only [map_sub,map_sum]; have he (i:ℕ)(hi:i<n): jumped L (raising j (launch (p k i)))=0:= larger (p k i).val _ (lt_of_lt_of_le hi hl) L; rw [sum_eq_zero (fun i (hi:i∈range n)=> he i (mem_range.mp hi)),sub_zero]
lemma arm_K (j:Axis)(p:Long G) : orderK j (arm n p)=0:= by rw [arm_point,map_sum]; exact sum_eq_zero fun i _=> K_bound ..

def Fill (R:ℕ→ℕ)(C:ℕ→ℝ)(n m:ℕ)(A:ℕ→Brush G) (B:ℕ→Long G): Prop:= ∀ k≤n, Bark R C k (n-k+m) (fun i=>A i-arm n (B i))
lemma replenish (hr:Tendsto R atTop atTop)(h:Bark R C n m A)(hp:ClearK A): ∃ B:ℕ→Long G, Fill R C n m A B:= by
    induction n generalizing m A with
    | zero=> refine ⟨0,fun k hk=>?_⟩; have he:k=0:=(by omega); subst k; simpa only [arm_point,range_zero,sum_empty,sub_zero,Nat.sub_zero,zero_add]
    | succ n IH=>
       let c (k):=reachL n (A k); let f(k):= A k-launch (c k); obtain ⟨B,hB⟩:=IH (shrank hr h hp) (hp.gr (tree c))
       change Fill _ _ _ _ f B at hB
       let Y(t:ℕ):Long G:=Function.update (B t) n (c t); refine ⟨Y,?_⟩
       have he : (fun i=> A i-arm (n+1) (Y i))=(fun i=> f i-arm n (B i)):= by
           funext i; rw [arm_succ,arm_point,arm_point]; have hv:∑ z∈ range n, launch (Y i z)=∑ z∈ range n, launch (B i z):= sum_congr rfl (fun z hz=>congr_arg _ (Function.update_of_ne (Nat.ne_of_lt (mem_range.mp hz)) ..)); rw [hv]; unfold Y f; rw [Function.update_self]; abel
       intro k hk; rcases eq_or_lt_of_le hk with rfl|hv
       · rw [Nat.sub_self,zero_add]; exact h.arm_sub Y le_rfl
       rw [he, show n+1-k+m=n-k+(m+1) from by omega]; exact hB k (Nat.le_of_lt_succ hv)

-- Limit class normalized shrink. Basis finite: if injective ✔ preserves limits.
variable {B:ℕ→Long G}
def Released (f:ℕ→V):Prop:= ∃ v:V,Tendsto f atTop (𝓝 v)
namespace Released
lemma zero : Released (0:ℕ→V):=⟨0,tendsto_const_nhds⟩
variable {f g:ℕ→V}
lemma add (h:Released f)(p:Released g):Released (f+g):=by obtain ⟨x,h⟩:=h;obtain ⟨y,p⟩:=p;exact ⟨x+y,h.add p⟩
lemma sub (h:Released f)(p:Released g):Released (f-g):=by obtain ⟨x,h⟩:=h;obtain ⟨y,p⟩:=p; exact ⟨x-y,h.sub p⟩
lemma old (h:Released f): f=O[Fℕ] (fun _:ℕ=> (1:ℝ)):= by obtain ⟨x,h⟩:=h; exact h.isBigO_one ℝ -- name
lemma smul {a:ℕ→ℝ}(hf:Released f)(ha:Released a): Released (a • f):= by obtain ⟨x,h⟩:=hf;obtain ⟨y,ha⟩:=ha;exact ⟨y • x, ha.smul h⟩ -- Pi.smul pi pointwise?
variable {W:Type*}[NormedAddCommGroup W][NormedSpace ℝ W]
lemma lin (L:V→ₗ[ℝ] W)[FiniteDimensional ℝ V](h: Released f): Released (L ∘ f):= by obtain ⟨x,h⟩:=h; exact ⟨L x,L.toContinuousLinearMap.continuous.continuousAt.tendsto.comp h⟩
lemma pinj [FiniteDimensional ℝ W](L:V→ₗ[ℝ] W)(hl:Function.Injective L)(h:Released (L ∘ f)): Released f:= by
    have he:f=L.leftInverse ∘ (L ∘ f):=funext fun k=> (L.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr hl) (f k)).symm; rw [he]; exact lin _ h
lemma piR {I:Type*}[Fintype I]{f:ℕ→I→V}(h:∀ i, Released (fun k=> f k i)): Released f:= by choose c hc using h; exact ⟨c,tendsto_pi_nhds.mpr hc⟩
lemma sumR {I:Type*}(p: Finset I){a:ℕ→I→V}(h:∀ i∈p, Released (fun k=>a k i)): Released (fun k=>∑ i∈p,a k i):= by
    classical
    induction p using Finset.induction_on with
    | empty=> simp only [sum_empty];exact zero
    | insert i p hi IH=> simp_rw [sum_insert hi]; exact (h i (mem_insert_self ..)).add (IH (fun k hk=> h k (mem_insert_of_mem hk)))
lemma reduce (hc:∀ᶠ i in Fℕ,e i≠0)(he:Tendsto e atTop (𝓝 0))(h:(f=O[Fℕ] (fun i=> e i^k)))(hm:m<k):
    Tendsto (fun i=>((e i)^m)⁻¹ • f i) atTop (𝓝 0):= by
   let r i:= ((e i ^ m)⁻¹)
   have ht : (fun i=> r i • f i)=O[Fℕ] (fun i=>e i^(k-m)) := by
      have hg: ∀ᶠ i in Fℕ, r i * e i^k=e i^(k-m):= hc.mono fun i hi=> by rw [show e i ^ k=e i^m *e i^(k-m) from by rw [← pow_add];congr;omega]; unfold r; rw [inv_mul_cancel_left₀ (pow_ne_zero _ hi)]
      exact (((isBigO_refl r Fℕ).smul h).congr' EventuallyEq.rfl hg)
   refine ht.trans_tendsto ?_; convert he.pow (k-m) using 1; simp [zero_pow (show k-m≠0 from by omega)] -- edit
end Released

abbrev sampleP (n:ℕ)(j:Axis)(l : Fin k→Axis): Okay G n→ₗ[ℝ] G.Color:= (LinearMap.proj (0:Cover)) ∘ₗ jumped l ∘ₗ raising j ∘ₗ valP n
def ex (n:ℕ): Okay G n→ₗ[ℝ] Line G n := LinearMap.pi fun j:Axis=> LinearMap.pi fun l=> sampleP n j l
lemma ex_in (n:ℕ) : Injective (ex (G:=G) n):= by
    refine (@LinearMap.ker_eq_bot ℝ ℝ (Okay G n) (Line G n) _ _ _ _ _ _ _ (ex (G:=G) n)).mp ?_; rw [eq_bot_iff]; intro p hp; obtain ⟨p,h⟩:= p; change _=0; apply Subtype.ext; apply Subtype.ext; funext j; apply seedEq; intro i
    have he:= congr_fun (congr_fun (LinearMap.mem_ker.mp hp) j) i;change jumped i (raising j (port n p)) 0=(0:G.Color) at he; rw [eg,jumpIt,top] at he; exact (smul_eq_zero.mp he).resolve_left (by positivity); exact p.sym j
lemma arm_eating (hr:Tendsto R atTop atTop)(he:∀ i,0<e i)(hg:Tendsto e atTop (𝓝 0))(h:Fill R (fun i=>e i^(n+1)) n m A B)(hp:∀ k:ℕ,k<n→∀ (j:Axis)(l:Fin k→Axis),Released (fun i=> (e i^(k+1))⁻¹ • jumped l (raising j (A i)) 0)) :
    ∀ k:ℕ,k<n→ Released (fun i=> (e i^(k+1))⁻¹ • B i k):= by
   intro k hk
   let f (m i:ℕ):= (e i^(m+1))⁻¹
   let g (m:ℕ):=Released (fun i=> f m i • B i m)
   have he' (i:ℕ) (p:i≤n):∀ k, i≤k→ k<n→g k:= by
      induction p using Nat.decreasingInduction with
      | self=> intros; omega
      | of_succ i hi IH=>
         intro s hs hy; rcases eq_or_lt_of_le hs with heq|hle
         · subst s; unfold g
           let L := ex (G:=G) i; apply Released.pinj L (ex_in (G:=G) i);apply Released.piR; intro j; apply Released.piR; intro l
           let F:Brush G →ₗ[ℝ] G.Color:= (LinearMap.proj (0:Cover)) ∘ₗ jumped l ∘ₗ raising j
           have Hr : Tendsto (fun t=> f i t • F (A t-arm n (B t))) atTop (𝓝 0):= Released.reduce (Eventually.of_forall fun t=>(he t).ne') hg (show (fun t=> F (A t-arm n (B t)))=O[Fℕ] (fun t=>e t^(n+1)) from (h i hi.le j l).ground (hr.eventually (eventually_ge_atTop _))) (by omega)
           let G' (d t:ℕ):= f i t • sampleP d j l (B t d)
           have hh (d:ℕ)(hb:d>i)(hn:d<n): Released (G' d):= by
               have ht:e=O[Fℕ] e:= isBigO_refl ..
               have he:G' d=(fun t=> e t^(d-i)) • (sampleP d j l ∘ (fun t=> f d t • B t d)):= by
                   funext t; change f i t • sampleP d j l (B t d)= e t^(d-i) • sampleP d j l (f d t • B t d); rw [map_smul,smul_smul];unfold f; apply congr_arg (· • sampleP d j l (B t d)); rw [show e t^(d+1)= e t^(d-i)*e t^(i+1) from by rw [← pow_add,show d-i+(i+1)=d+1 by omega]]; field_simp [(he t).ne']
               rw [he]; exact (Released.lin _ (IH d hb hn)).smul ⟨(0:ℝ)^(d-i),hg.pow _⟩
           have hz(d:ℕ)(hb:d < i): G' d=0:= by funext t; unfold G'; rw [show sampleP d j l (B t d)=(0:G.Color) from congr_fun (larger (B t d).val j hb l) 0,smul_zero]; rfl
           let P:= (range n).erase i
           have hv : Released (fun t=>∑ d∈P,G' d t):= by
               apply Released.sumR P; intro d hd; obtain ⟨he,h⟩:=mem_erase.mp hd; rcases lt_or_gt_of_ne he with H|H
               · rw [hz d H]; exact Released.zero
               exact hh d H (mem_range.mp h)
           have HZ : Released (fun t=> f i t • F (A t-arm n (B t))) := ⟨0,Hr⟩; refine Eq.mp (congr_arg Released ?_) (((hp i hy j l).sub HZ).sub hv)
           funext t; simp only [map_sub, smul_sub,Pi.sub_apply];
           change f i t • F (A t)-(f i t • F (A t) - f i t • F (arm n (B t))) -(∑ d∈P,G' d t)= sampleP i j l ((fun i_1=>_ • _) t); rw [arm_point,map_sum,smul_sum]
           rw [show ∑ d∈range n,f i t • F (launch (B t d))= ∑ d∈range n,G' d t from rfl];
           rw [← add_sum_erase _ _ (mem_range.mpr hy)];
           rw [map_smul]; change _-(∑ d∈P,G' d t)= G' i t; unfold P; abel
         exact IH s hle hy
   exact he' k hk.le k le_rfl hk
end YM.PositionX.Reed
