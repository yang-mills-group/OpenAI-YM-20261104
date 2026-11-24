import YM.MSbar.Image.Reader
/-! Exp and finite parts (momentum dilation stances).
 The regulator-polynomial pair is computed AFTER exponential reweightings. No concession on analytic dependence.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Image
open Dim Symbol Domain Diagram Function Set Filter Play Play.Deck Category Counter Super Scale Counter.Crest Complex Metric Asymptotics Finset
open scoped Classical Topology BigOperators
variable {C:Type} {U:Set ℂ} {W:Edition C} {d:Bit} {F G: Film C} {x:ℂ}
namespace TokenTrain
def trunc (n:ℕ)(x:ℂ):ℂ:=∑ i∈scope n, x^i/(i.factorial:ℂ)
def tail (n:ℕ)(x:ℂ):ℂ := (Complex.exp x-trunc n x)/x^n
lemma begins (n:ℕ): trunc n 0=1:=by induction n with | zero=>simp [trunc,scope] | succ n ih=> rw [trunc,sum_range_succ]; simp [trunc,scope] at ih ⊢; exact ih
lemma splitter (n:ℕ) : tail n x*x^n=Complex.exp x-trunc n x:= by by_cases h:x=0; simp [tail,h,begins]; exact div_mul_cancel₀ _ (pow_ne_zero _ h)
lemma value (n:ℕ): tail n 0=0:= by simp [tail,begins]
lemma diff (n:ℕ):Differentiable ℂ (tail n):=by
    have ht : Tendsto (tail n) (𝓝 0) (𝓝 0):= (Complex.exp_sub_sum_range_succ_isLittleO_pow n).tendsto_div_nhds_zero
    rw [← differentiableOn_univ]; refine (Complex.differentiableOn_compl_singleton_and_continuousAt_iff (c:=0) univ_mem).mp ⟨fun x hx=> ?_,?_⟩
    · apply DifferentiableAt.differentiableWithinAt; have hv:x^n≠0:= pow_ne_zero _ (show x≠0 from hx.2); unfold tail trunc; fun_prop (disch:=assumption)
    simpa [ContinuousAt,value n] using ht
end TokenTrain
open TokenTrain
variable [Profit U] {n i k:ℕ}(a:ℂ)
def rides (a:ℂ)(i:ℕ)(v:ℕ)(z:ℂ):ℂ:= Complex.exp (a*Scale.slope v z)*step v i z
def follow (a:ℂ)(i k:ℕ)(F:Film C): Functionals C:=∑ v∈ scope k, times (rides a i v) (F v)
-- split into finite poles & regular zero. Use Count only.
def chip (x:ℂ) (n:ℕ): ℂ:= x^n/(n.factorial:ℂ)
def lag (a:ℂ)(n:ℕ)(v:ℕ)(z:ℂ):ℂ:= a^n*tail n (a*Scale.slope v z)
def rail (a:ℂ)(i n v:ℕ): ℂ→ℂ:= fun z=>∑ j∈scope n, chip a j * step v (j+i) z
lemma tracks (n v:ℕ): rides a i v x= rail a i n v x+ lag a n v x*step v (n+i) x:= by
    unfold rides; rw [show cexp (a*Scale.slope v x)= tail n (a*Scale.slope v x) * (a*Scale.slope v x)^n + trunc n (a*Scale.slope v x) from (by rw [splitter (x:=_) n]; abel)]; unfold rail lag; rw [add_comm,add_mul]; congr! 1
    · unfold trunc; rw [sum_mul]; apply Finset.sum_congr rfl; intro j _; unfold chip step; rw [pow_add,mul_pow]; ring
    unfold step; rw [pow_add, mul_pow]; ring
lemma journey (n:ℕ)(F:Film C): follow a i k F=(∑ j∈ scope n, chip a j • scan (j+i) (scope k) F)+ (∑ v ∈ scope k, times (lag a n v) (times (step v (n+i)) (F v))):=by
    funext z; simp only [follow, Finset.sum_apply,times,Pi.add_apply,Pi.smul_apply,scan,Finset.smul_sum, tracks a n, add_smul, mul_smul, rail, step, Finset.sum_add_distrib,Finset.sum_smul]; rw [Finset.sum_comm]
variable (h:Ready U W d k F)
-- analytic stances and finite projected formula
omit [Profit U] in
lemma lagged : DifferentiableOn ℂ (lag a n i) U:= DifferentiableOn.const_mul ((TokenTrain.diff _).comp_differentiableOn ((holistic _ i).const_mul _)) _
include h
lemma flight : Regular U W d (follow a i k F):= by obtain ⟨n,H⟩:= h.room; rw [journey a n]; exact Price.add (Price.sum _ (fun j _=> Price.scale (h.marks _) _)) (Price.sum _ (fun j _=> (Counter.Crest.after (H j) (by omega : n ≤ n+i)).unit (lagged a))) -- include h
include h
lemma ticket (H:∀ i, Price n U W d (F i)): reader U W d (follow a i k F)=∑ j∈scope n, chip a j • reader U W d (scan (j+i) (scope k) F):=by
    let K(v:ℕ):= times (step v (n+i)) (F v); have hk(v:ℕ): Regular U W d (K v):= after (H v) (by omega); rw [journey a n]
    have hK(v:ℕ): Regular U W d (times (lag a n v) (K v)):= (hk v).unit (lagged _)
    have ht(j:ℕ): Regular U W d (chip a j • scan (j+i) (scope k) F):=(h.marks _).scale _
    rw [Reader.plus (Price.sum _ (fun j _=> ht j)) (Price.sum _ (fun j _=>hK j)),Reader.sum _ (fun j _=> ht j),Reader.sum _ (fun j _=> hK j)]; simp_rw [Reader.times (h.marks _)]; rw [show (∑ v∈scope k, reader U W d (times (lag a n v) (K v)))=0 from Finset.sum_eq_zero (fun v _=> ?_),add_zero]; rw [Reader.holm (hk v) (lagged _)]; simp [lag, TokenTrain.value, Scale.slope]
end YM.MSbar.Image
