import YM.PertExtension.FlowMilk

/-! Split-and-restore estimate for Gaussian multi-point mark overlaps.
Polynomial coefficients and propagator bounds tracked separately and with
independent formal basis weights.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace YM.PertExtension.BlendAsymptotic
open Filter Set Function Finset MvPolynomial Next.Rank Normal PolyFlow
open scoped Topology ContDiff Classical BigOperators
variable {ι V A W Z:Type*}{l:Filter ι}{s:Finset A}

lemma Close.pot {f:ι→A→poly V}{q:A→poly V}{m:ι→ℂ}(h:∀ i∈s,Close (fun k=>f k i) (q i) m l) : Close (fun k=>Normal.pot s (f k)) (Normal.pot s q) m l := by
    unfold Normal.pot; induction s using Finset.induction_on with
    | empty=>simp [Close.const]
    | @insert i t ht ih=>simp_rw [prod_insert ht]; exact ((h i (by simp)).operator (T:=(post (V:=V) i).toLinearMap) (R:=(fun _=> (post (V:=V) i).toLinearMap)) (fun _=> Close.const)).mul' (ih fun a ha=> h a (by simp [ha]))
lemma Limit.pot {f:ι→A→poly V}{q:A→poly V}(h:∀ i∈s,Limit (fun k=>f k i) (q i) l) : Limit (fun k=>pot s (f k)) (pot s q) l := (Close.pot (m:=0) (fun i hi=>empty_close (h _ hi))).toLimit

lemma pot_price (p:A→poly V)(r:ℂ)(w:A→ℕ) (u:V→Z→₀ℂ) :
     pot s (fun i=> r^w i • exchange u (p i))= r^(∑ i∈s,w i) • exchange (perSlot (fun _=>u)) (pot s p):=by
  unfold pot
  simp only [_root_.map_prod,posts,_root_.map_smul,← C_mul',←mul_pow, ←prod_pow_eq_pow_sum, prod_mul_distrib, map_prod, _root_.map_pow, _root_.map_mul,post_C]

protected lemma subtract_home (K : Symmetric (A×V))(M : A→Symmetric V)(p : A→poly V): blend K 0 (pot s p)= blend (K+ -(self M)) 0 (pot s (fun i=> milk (M i) (p i))):=by
   have he i: milk (-(M i)) (milk (M i) (p i))=p i:= by rw [warms,show -(M i)+M i=0 from Symmetric.ext (neg_add_cancel _),froze]
   rw [← barn];exact congr_arg (blend K 0 ∘ pot s) ((funext he).symm)

def sliceK {Y:Type*}(K:Symmetric (A×Y))(i:A): Symmetric Y:=⟨(fun x y=>K.cov (i,x) (i,y)),fun _ _=>K.symm ..⟩
def onlyCross (K:Symmetric (A×V)):= K + -(self (sliceK K))
lemma only_mixed (K:Symmetric (A×V))(a b:A×V): (onlyCross K).cov a b = if a.1=b.1 then 0 else K.cov a b := by
   unfold onlyCross; change K.cov a b + -(if a.1=b.1 then ((K.cov (a.1,a.2) (a.1,b.2))) else 0)=_;split_ifs with h
   · simp [show (a.1,b.2)=b by rw [h],add_neg_cancel]
   simp
variable {K : ι→Symmetric (A × V)}(T:Symmetric V) (p : A → poly V)
local notation "D" => (onlyCross ∘ K)
local notation "F" => (fun i=>milk T (p i))
variable {r : ι→ℝ}(w:A→ℕ)
variable (h₀: ∀ a i j d, rate_as (fun k=>((sliceK (K k) a).cov i j)) (T.cov i j) (fun k=>(r k:ℂ)^d) l) (hc : PolyFlow.Bounded (onlyCross ∘ K) l)
variable {u:ι→V→W→₀ℂ}{H:ι→Symmetric (A×W)}(σ:Z→W)(q':A→poly Z)(Q:Symmetric (A×Z))
variable (hh : ∀ k,(onlyCross (K k))=scope (perSlot (fun _=>u k)) (H k))(hH : PolyFlow.Bounded H l) (hq : ∀ i∈s,Limit (fun k=> ((r k:ℂ)^w i) • exchange (u k) (milk T (p i))) (rename σ (q' i)) l) (hL : ∀ (a b:A×Z),Tendsto (fun k=>(H k).cov (a.1,σ a.2) (b.1,σ b.2)) l (𝓝 (Q.cov a b)))
include h₀ hc s hh w hH hq hL
lemma accumulate :
    Tendsto (fun k=> ((r k:ℂ)^(∑ i∈s,w i)) • blend (K k) 0 (pot s p)) l (𝓝 (blend Q 0 (pot s q'))) := by
   let G (k) i:= milk (sliceK (K k) i) (p i)
   let b i:= milk T (p i); let d:=∑ i∈s,w i
   let n(k):=(r k:ℂ)^d
   have hclose: Close (fun k=>pot s (G k)) (pot s b) n l:= Close.pot (fun i _=>by exact milk_close (K:=fun k=>sliceK (K k) i) (fun a b=>h₀ i a b d) (p i))
   let a k:= blend (K k) 0 (n k • pot s p)
   let trueval k:= blend (D k) 0 (n k • pot s b)
   have hdiff:= blend_fading hc hclose.diff
   have hdif: Tendsto (a-trueval) l (𝓝 0):= hdiff.congr (fun k=>by
      rw [_root_.map_smul,_root_.map_sub]
      unfold a trueval; simp [BlendAsymptotic.subtract_home (K k) (M:=sliceK (K k)) p,smul_sub,b,map_smul, onlyCross, mul_sub,G]
   )
   let hP:= Limit.pot (s:=s) hq
   let foreign (k) i :=((r k:ℂ)^w i) • exchange (u k) (b i)
   let oracle := pot s (fun i=>rename σ (q' i))
   let lift(k x):= blend (H k) 0 x
   have heq k: trueval k= lift k (pot s (foreign k)):= by
         unfold lift trueval foreign
         have he:= pot_price (p:=b) (r k:ℂ) w (u k) (s:=s)
         simp only [he, map_smul, wets,← hh k]
         rw [← show reads (perSlot (fun _ : A =>u k)) (0 : A × W → ℂ)=0 from funext fun x=>?_]
         rfl
         simp [reads]
   let hqfixed(k):=lift k oracle
   let liftV : A×Z → A×W := fun x=>(x.1,σ x.2)
   have hor : oracle=rename liftV (pot s q'):= by
      unfold oracle pot; rw [map_prod] ;refine prod_congr rfl fun i hi=>?_ ;unfold Normal.post;dsimp only;rw [rename_rename,rename_rename];rfl
   let LQ (k):=scope (fun x=>Finsupp.single (liftV x) 1) (H k)
   have hq0 : Tendsto hqfixed l (𝓝 (blend Q 0 (pot s q'))) := by
      unfold hqfixed -- adjust
      simp_rw [lift,hor,Normal.labelled liftV,wets,show reads (fun x=>(Finsupp.single (liftV x) 1)) (0 : A × W → ℂ)=0 from funext fun i=>by simp [reads]]
      exact blend_limit (Q:=Q) (K:=LQ) (by simp_rw [LQ,match_name]; exact hL) Limit.const
   have lim : Limit (fun k=>pot s (foreign k) - oracle) (0:poly _) l:= by
       simpa [foreign,oracle,b, sub_eq_add_neg] using! hP.add (Limit.const (l:=l) (p:=oracle)).neg
   have hex:Tendsto (trueval-hqfixed) l (𝓝 0):= by
     have he:=blend_fading hH lim
     exact he.congr fun k=>by rw [_root_.map_sub, show blend _ _ (pot s (foreign k))=trueval k from (heq k).symm];rfl
   have hz := hdif.add (hex.add hq0)
   replace hz: Tendsto (fun k=>a k-trueval k+(trueval k-hqfixed k + hqfixed k)) l _:=hz
   rw [zero_add,zero_add] at hz
   exact hz.congr fun k=>by rw [sub_add_cancel,sub_add_cancel];unfold a n d; exact _root_.map_smul ..

end YM.PertExtension.BlendAsymptotic
