import YM.RG12.Strike.Bore
/-!
# Separated fundamental line and all potential jet data on it
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Strike
open Function Set Filter MeasureTheory Real Finset
open scoped Topology InnerProductSpace ContDiff BigOperators Classical
abbrev puncture:Set R:=({0}:Set R)ᶜ
lemma punct_open:IsOpen puncture:=isOpen_compl_singleton
lemma punct_field : silk puncture field:=fun _ hx=>gField hx
lemma black_nonzero {x:R}(hx:x≠0) :black x≠0:=by unfold black;exact_mod_cast (show (‖x‖^2:ℝ) ≠ 0 by positivity [norm_pos_iff.mpr hx])
lemma second {x:R}(hx:x≠0)(i j:Axis4): barrage field [i,j] x = 8*(black x)^(-3:ℤ)*(x i:ℂ)*(x j:ℂ)-(if i=j then 2*(black x)^(-2:ℤ) else 0):=by
   have he(k:R)(h:k≠0): barrage field [j] k=(drip (pin [j])) k:=by
      have hA:field=(fun z:R=>(black z^1)⁻¹):=by ext; unfold field; rw [pow_one]
      rw [barrage,barrage, hit,hA,(negative j k 1 h).deriv]; unfold drip pin; simp only [sun_step,sun_nil,mul_one,List.length_cons,List.length_nil,coefficient,Nat.cast_zero,Nat.cast_one,zero_add]
   have hp: (barrage field [j] ∘ palette i x) =ᶠ[𝓝 (0:ℝ)] (drip (pin [j]) ∘ palette i x):=by
      have hh : Tendsto (palette i x) (𝓝 (0:ℝ)) (𝓝 x):=by nth_rw 2 [show x=palette i x 0 from (born ..).symm]; exact (drawing x i).continuousAt
      exact (hh.eventually_ne hx).mono fun y h=> he _ h
   unfold barrage hit; -- unfolds inner? rf
   change deriv (barrage field [j] ∘ palette i x) 0=_
   rw [hp.deriv_eq,(changeAt i x (pin [j]) hx).deriv]; by_cases h:i=j
   all_goals have hz: (↑‖x‖:ℂ)≠0:=by exact_mod_cast (norm_pos_iff.mpr hx).ne'
   all_goals simp [h,flourish,pin,pluck,scripts,sun_step,sun_nil,drip,coefficient, eq_comm, ←inv_pow]; norm_num [zpow_neg]; simp only [← inv_pow]; field_simp <;> try ring
lemma massless (x:R)(hx:x∈puncture): ∑ i:Axis4,barrage field [i,i] x=0:=by
   let b:=black x; let q:=EuclideanSpace.basisFun Axis4 ℝ
   have hi := q.sum_sq_inner_right x -- which? right lemma
   have hr : ∑ i:Axis4,x i ^2 = ‖x‖^2:=by
      simp only [← project x]; exact q.sum_sq_inner_right _
   simp_rw [second hx,if_true, sum_sub_distrib, mul_assoc,← sq, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,nsmul_eq_mul];simp only [Axis4,Fintype.card_fin]
   rw [show (∑ i:Fin 4,(↑(x i) :ℂ)^ (2:ℕ))=b from ?_]
   · change 8*(b^(-3:ℤ)*b)-2*((↑(4:ℕ):ℂ)*b^(-2:ℤ))=0
     have hb:b ≠ 0:=black_nonzero hx; norm_num; field_simp;try ring
   unfold b black; exact_mod_cast hr

-- full derivative cylinder norms. spend permutation invariance across lists inside bore.
lemma rain_spin (f:R→ℂ){S:Set R}(hS:IsOpen S)(he:silk S f){v u:Cells}(h: List.Perm v u)(x:R)(hx:x∈S):barrage f v x=barrage f u x:=regimen hS he hx h
lemma borne {ι:Type}(T:Finset ι){S:Set R}(hs:IsOpen S)(f:ι→R→ℂ)(h:∀ i∈T,silk S (f i))(L:Poke)(x:R)(hx:x∈S):
    barrage (∑ i ∈ T,f i) L x=∑ i∈T,barrage (f i) L x:=by
   induction L generalizing x with
   | nil=>change (∑ i∈T,f i) x =_; simp [barrage]
   | cons a b he=>
     let g:= fun i:ι=> barrage (f i) b
     change hit a (barrage _ b) x=∑ i∈ T,hit a (g i) x
     have hQ (i)(hr:i∈T):silk S (g i):=vellum hs (h i hr) b
     apply (in_turn (f:=barrage _ b) (g:=∑ i∈T,g i) hs hx a (fun y hy=>by simpa only [Finset.sum_apply] using! he y hy)).trans
     exact thread hx T _ hQ _
lemma bore_scale (c:ℂ){S:Set R}(hs:IsOpen S)(f:R→ℂ)(L:Poke)(x:R)(hx:x∈S): barrage (fun x=>c*f x) L x=c*barrage f L x:=by
    induction L generalizing x with
    | nil=> rfl
    | cons i a ha=> exact (in_turn (g:=fun y=>c*barrage f a y) hs hx i ha).trans (Strike.spin c (barrage f a) i)
lemma vanes (L:Poke)(x:R)(hx:x≠0):∑ i:Axis4,barrage field (i::i::L) x=0:=by
    let f(i:Axis4):= barrage field [i,i]; have he(i):silk puncture (f i):=vellum punct_open punct_field _
    have hh : ∀ x∈ puncture,(∑ i,f i) x=(0:R→ℂ) x:=fun x hx=> (Finset.sum_apply ..).trans (massless x hx)
    have hr i: barrage field (i::i::L) x=barrage (f i) L x:=by
       rw [show f i = _ from rfl,← barrage_append]; apply rain_spin field punct_open punct_field (List.perm_append_comm (l₁:=[i,i]) (l₂:=L)) x hx
    simp only [hr]; rw [← borne univ punct_open _ (fun i _=>he i) _ _ hx,barrage_local punct_open hx hh,barrage_zero _ _]
-- symmetric trace calculus commutes FULL. supports external list.
variable (E : Axis4→R→ℂ){S:Set R}(hs:IsOpen S)(he:∀ i,silk S (E i))
structure Breeze (E : Axis4 → R → ℂ)(S:Set R) : Prop where
   harmony(x:R)(hx:x∈S): ∀ j:Axis4,∑i:Axis4,barrage (E j) [i,i] x=0
   diverge(x:R)(hx:x∈S): ∑i:Axis4,barrage (E i) [i] x=0
def slate (E: Axis4 → R → ℂ)(x:R):Poll:=fun i d=>barrage (E i) d x
include hs he
lemma jets (H:Breeze E S)(x:R)(hx:x∈S)(n:ℕ):Clean (slate E x) n:=by
  constructor
  · intro i; constructor
    · intro v u h _; exact rain_spin (E i) hs (he _) h x hx
    · intro u _;let f(j:Axis4):=barrage (E i) [j,j]
      have hh:∀ x∈S,(∑ i,f i) x=(0:R→ℂ) x:=fun x hx=> (Finset.sum_apply ..).trans (H.harmony x hx i)
      have hr j: slate E x i (j::j::u)=barrage (f j) u x:=by
         unfold f; rw [← barrage_append]; apply rain_spin (E i) hs (he _) (List.perm_append_comm (l₁:=[j,j]) (l₂:=u)) x hx
      simp_rw [hr];rw [← borne univ hs _ (fun i' _=> vellum hs (he i) _) _ _ hx,barrage_local hs hx hh,barrage_zero _ _]
  intro u _;let f(i:Axis4):=barrage (E i) [i]
  have hh:∀ x∈S,(∑ i,f i) x=(0:R→ℂ) x:=fun x hx=> (Finset.sum_apply ..).trans (H.diverge x hx)
  have hr i: slate E x i (i::u)=barrage (f i) u x:=by
         unfold f; rw [← barrage_append]; apply rain_spin (E i) hs (he _) (List.perm_append_comm (l₁:=[i]) (l₂:=u)) x hx
  simp_rw [hr]; rw [← borne univ hs _ (fun i _=> vellum hs (he i) _) _ _ hx,barrage_local hs hx hh,barrage_zero _ _]
-- literal exterior potential on a vertex-to-exterior line, at displacement FROM mark to vertex; any
-- derivative signs in external mark absorbed into T. Adapt to any jet labels/potential props later.
omit hs he
variable (T:Foil)(ht:anti T)(u v:Cells)
abbrev cloud (T:Foil)(u:Cells)(i:Axis4):R→ℂ:= leg T u i []
lemma cloud_silk (i):silk puncture (cloud T u i):=by
   intro x hx; apply ContDiffAt.sum (s:=univ)
   intro j _; exact contDiffAt_const.mul (vellum punct_open punct_field _ x hx)
lemma ridges (i)(x:R)(hx:x∈puncture): barrage (cloud T u i) v x=∑ j:Axis4,2*T j i*barrage field (v++(u++[j])) x:=by
   unfold cloud leg; rw [show (fun x => ∑ j:Axis4,2*T j i *tube _ x)=(∑ j:Axis4, fun x=>2*T j i * tube ([]++u++[j]) x) from funext fun x=> by simp]
   rw [borne univ punct_open _ _ _ _ hx]
   · refine sum_congr rfl ?_;intro j _; unfold tube;rw [bore_scale _ punct_open _ _ _ hx,←barrage_append,List.nil_append]
   intro j _ y hy; exact contDiffAt_const.mul (vellum punct_open punct_field _ y hy)
include ht
lemma breezes : Breeze (cloud T u) puncture:=by
   constructor
   · intro x hx i; simp_rw [ridges _ _ _ _ _ hx]; rw [sum_comm]; apply sum_eq_zero; intro j _
     rw [← mul_sum]; refine mul_eq_zero_of_right _ (Strike.vanes (L:=u++[j]) _ hx)
   intro x hx
   simp_rw [ridges _ _ _ _ _ hx,List.cons_append,List.nil_append]
   -- swap j and i; symmetry kills via commute differentiations
   let f(i j:Axis4):ℂ:=barrage field (i::(u++[j])) x
   have hf(i j:Axis4): f i j = f j i :=by
      have he(i j:Axis4):List.Perm (i::(u++[j])) (i::j::u):=List.Perm.cons i (by convert (List.perm_append_comm (l₁:=u) (l₂:=[j])) using 1; simp)
      exact rain_spin field punct_open punct_field ((he ..).trans ((List.Perm.swap j i u).trans (he ..).symm)) x hx
   change ∑i:Axis4,∑j:Axis4,2*T j i*f i j=0
   let s (i j:Axis4):=2*T j i*f i j
   let p:= ∑i:Axis4,∑j:Axis4,s i j
   have he: p= -p:=by
       unfold p; simp_rw [← Finset.sum_neg_distrib]; rw [sum_comm]; apply sum_congr rfl;intro i _; apply sum_congr rfl;intro j _; unfold s; rw [ht i j,hf j i]; ring
   change p=0;linear_combination 1/2*he
end YM.RG12.Strike
