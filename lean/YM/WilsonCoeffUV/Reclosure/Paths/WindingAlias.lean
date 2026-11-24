import YM.WilsonCoeffUV.Reclosure.Selection
/-!
# Periodization on local primitives EXACT, including any winding aliases

This is for the germ carried to Side n, all positive ranks, multiplying
by counting *sites* if scalar handled separately. Not for the once pushed
vacuum: a line times a vertex at n is generally a product of periodizations,
not their product periodized. No IR quotient in these statements.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank.Mosaic
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power Stationary
open scoped ContDiff Topology BigOperators
variable {G:Gauge}{c:Side}{N M e m i k r t:ℕ}{I U α : Type*}

-- The residue price of a monomial under any rank-positive stencil.
def residue {U α:Type*} [AddCommGroup U] [DecidableEq U][DecidableEq α] (b:I→U×α)
     (y:U) (x:Fin (t+1)→ U×α)(z:Fin (t+1)→ I) (c:ℝ):ℝ:= if x= jog y ∘ (b ∘ z) then c else 0
lemma residue_hit [AddCommGroup U][DecidableEq U][DecidableEq α]
    (b:I→ U×α) (y:U)(x:Fin (t+1)→ U×α)(z)(c:ℝ) :
    (∏ i:Fin (t+1), plank (U:=U) (some ∘ b) y (z i) (x i)) • c=residue b y x z c:=by
    simp_rw [plank_origin (b:=some ∘ b) y (z _) (show (some ∘ b) _=_ from rfl)]
    by_cases h:x=jog y ∘ (b ∘ z)
    · rw [residue,if_pos h]; subst x; simp
    obtain ⟨j,hj⟩:= Function.ne_iff.mp h
    rw [Finset.prod_eq_zero (Finset.mem_univ j) (Pi.single_eq_of_ne hj _), zero_smul,residue,if_neg h]
-- no alias counting penalty inside torus residue
lemma residue_at [AddCommGroup U] [DecidableEq U] [DecidableEq α] (b:I→U×α)(y:U)(x:Fin (t+1)→U×α)(z)(c:ℝ)
    (h:y ≠ (x 0).1-(b (z 0)).1) : residue b y x z c=0:= by
    apply if_neg; intro he; subst x; simp at h; apply h; change y=y+_-_; abel
lemma residue_sum [AddCommGroup U] [DecidableEq U][DecidableEq α] (b:I→U×α)(x:Fin (t+1)→ U×α)(z)(c:ℝ):
    HasSum (fun y=> residue b y x z c) (residue b ((x 0).1-(b (z 0)).1) x z c) := hasSum_single _ (fun _ hi=>residue_at _ _ _ _ _ hi)

-- unfolds BOTH dilutions match exactly
variable [Fintype I]
lemma cover_seed (b:I→YForest G)(x:Fin (t+1)→YForest G)(Q: Gen ℝ I) :
    sunflower (some ∘ b) Q (t+1) x = ∑ y, residue b ((x 0).1-(b (y 0)).1) x y (Q (t+1) y):=by
    let A:=fun y:Cover=>∑ i,residue b y x i (Q (t+1) i)
    let S:= (Equiv.funUnique (Fin 1) (Cover×ULift.{0} Unit)).trans (Equiv.prodUnique _ _)
    unfold sunflower worn
    rw [← S.symm.tsum_eq]
    trans ∑' y,A y
    · apply tsum_congr; intro y
      rw [tie]; split; · omega
      unfold iris fade; apply Finset.sum_congr rfl; intro i _
      exact residue_hit b y x i _
    exact (hasSum_sum fun i (_: i∈Finset.univ)=> residue_sum b x i _).tsum_eq
lemma tor_seed (b:I→YForest G)(X:stars G t c)(Q:Gen ℝ I): let u:=foldUnder c ∘ b
    wear (iris (some ∘ u) Q (t+1)) X=∑ y, residue u ((X 0).1-(u (y 0)).1) X y (Q (t+1) y):=by
    intro u; rw [iris_apply,Finset.sum_apply]; simp_rw [fade,residue_hit]
    rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun i _=>(HasSum.unique (hasSum_fintype _) (residue_sum u X i _))
section
variable (b:I→YForest G)(x:Fin (t+1)→I)(X:stars G t c)
open Classical in
/-- Winding of one term. -/
def launch (X:stars G t c)(w:Shift (Keys t))(A:ℝ): ℝ:=
    let a:=goose w (stH X) (stR X); if trope X w then residue b ((a 0).1-(b (x 0)).1) a x A else 0
omit [Fintype I] in
lemma location (X:stars G t c)(w:Shift (Keys t))(A:ℝ)(ht:w≠salvo (b ∘ x)): launch b x X w A=0:=by
    unfold launch
    let a:=goose w (stH X) (stR X); by_cases p:trope X w; swap; · simp [p]
    simp only [p,↓reduceIte]
    apply if_neg; intro hz
    change a=jog _ ∘ (b ∘ x) at hz
    apply ht; funext j; let l (i:Fin (t+1)):= Prod.fst (b (x i))
    have he : (a 0).1=0:= rfl
    have hu := congr_arg Prod.fst (congr_fun hz j.1.succ)
    change feetP w j.1.succ= ((a 0).1-(l 0))+l j.1.succ at hu
    rw [he,zero_sub,add_comm,←sub_eq_add_neg] at hu
    exact congr_fun (by simpa [feetP] using hu) j.2
omit [Fintype I] in
lemma launch_sum (A:ℝ): let y:= (X 0).1-wrap c (b (x 0)).1
    HasSum (fun w=>launch b x X w A) (residue (foldUnder c ∘ b) y X x A):=by
    classical
    intro y; let w:= salvo (b ∘ x); let M:=goose w (stH X) (stR X); let T:=foldUnder c ∘ b
    have hr: ((M 0).1:Cover)=0:=rfl
    have hx i: (M i).1= (b (x i)).1-(b (x 0)).1:= sole_salvo (b ∘ x) i
    have ht: (X= jog y ∘ (T ∘ x)) ↔ trope X w ∧ M=jog ((M 0).1-(b (x 0)).1) ∘ (b ∘ x):=by
       constructor
       · intro e; have he i : X i=(y+wrap c (b (x i)).1,(b (x i)).2):=congr_fun e i
         constructor
         · intro i; rw [he,he]; change _-_=wrap c (M i).1; rw [hx,map_sub]; simp
         funext i; refine Prod.ext ?_ (by have hh:=congr_arg Prod.snd (he i); exact hh)
         change _=((M 0).1-_)+_; rw [hx,hr]; abel
       rintro ⟨h,p⟩; funext i; refine Prod.ext ?_ (by have hh:=congr_arg Prod.snd (congr_fun p i); exact hh)
       specialize h i; change _=wrap c (M i).1 at h; rw [hx,map_sub] at h
       change _=(X 0).1-_+_; rw [sub_eq_sub_iff_add_eq_add] at h; exact (eq_sub_of_add_eq h).trans (by abel)
    have he: launch b x X w A=residue T y X x A:=by
       unfold launch; change (if trope X w then residue b _ M _ _ else 0)=_
       by_cases p:X= jog y ∘ (T ∘ x)
       · unfold residue; rw [if_pos p,if_pos (ht.mp p).1,if_pos (ht.mp p).2]
       unfold residue; rw [if_neg p]; by_cases h:trope X w; · rw [if_pos h, if_neg (fun H=> p (ht.mpr ⟨h,H⟩))]
       rw [if_neg h]
    rw [← he]; exact hasSum_single w (fun _ u=> location b x X _ A u)
end
lemma sunflower_wrap (b:I→YForest G)(Q:Gen ℝ I)(n:Side):let A:=sunflower (some ∘ b) Q (t+1)
    lagoon A n= wear (iris (some ∘ (foldUnder n ∘ b)) Q (t+1)):=by
    intro A; ext1 X; rw [tor_seed]; refine HasSum.tsum_eq ?_; expose_names
    have h (w:Shift (Keys t)): flair X A w=∑ i,launch b i X w (Q (t+1) i):=by
        by_cases H:trope X w
        · rw [flair_hit H]; change A _=_; unfold A; rw [cover_seed]; simp only [launch, H, ↓reduceIte]
        simp [flair_miss H,launch,H]
    change HasSum (flair X A) _; rw [funext h]
    exact hasSum_sum fun j (_: j∈Finset.univ)=> launch_sum b j X (Q (t+1) j)

variable {s v A B :ℝ}{F P:post G t}
lemma lagoon_plus (h:Amber terrain s A F)(p:Amber terrain v B P)(hv:0<s)(he:0<v)(n:Side):
   lagoon (F+P) n=lagoon F n+lagoon P n:=by
    funext x
    have ht : flair x (F+P)=fun i=> flair x F i+flair x P i:=by funext i; unfold flair; split; exacts [rfl,(add_zero _).symm]
    unfold lagoon; simp_rw [ht, Pi.add_apply]; rw [((flair_cost h hv x).unweighted (hinge_paid hv t).le).2.1.of_norm.tsum_add (((flair_cost p he x).unweighted (hinge_paid he t).le).2.1.of_norm)]
lemma lagoon_scalar (u:ℝ)(F:post G t)(n:Side): lagoon (u • F) n=u • lagoon F n:=by
    funext x
    have ht : flair x (u • F)=u • flair x F:=by funext i; simp only [Pi.smul_apply]; unfold flair; split; exacts [rfl,(smul_zero u).symm]
    unfold lagoon; rw [ht]; simp [Pi.smul_apply, tsum_mul_left]
lemma lagoon_none (n:Side): lagoon (0:post G t) n=0:=by simpa using lagoon_scalar 0 (0:post G t) n
omit [Fintype I] in
lemma lagoon_join {Q:I→post G t}(P:Finset I)(h:∀ i∈P, ∃ A:ℝ, Amber terrain s A (Q i))(he:0<s)(n:Side) : lagoon (∑ i∈P,Q i) n=∑ i∈P, lagoon (Q i) n:=by
    classical
    induction P using Finset.induction_on with
    | empty=> simp [lagoon_none]
    | @insert i P hi ih=>
      have H j (p:j∈P):= h j (Finset.mem_insert_of_mem p); have hv:=ih H
      -- for i∉P dummy default
      let C (j:I):= if p:j∈P then (H j p).choose else 0
      have ht j (p:j∈P): Amber terrain s (C j) (Q j):= by unfold C; rw [dif_pos p]; exact (H j p).choose_spec
      rw [Finset.sum_insert hi, Finset.sum_insert hi, lagoon_plus (h i (Finset.mem_insert_self ..)).choose_spec (Amber.sum _ ht) he he n,hv]
open Near
lemma wraps_atom (P:Atom G k)(t:ℕ)(n:Side): archInk P n (t+1)= lagoon (coverInk P (t+1)) n:=by
    let b (i:Near.Grid P):YForest G:=(i.1.1,i.2)
    have hb : some ∘ b=lead P:=rfl
    simp only [coverInk,←hb]; rw [sunflower_wrap b,iris_apply]
    unfold archInk; exact Finset.sum_congr rfl fun i _=> frames P i _
lemma wraps_series {X:ℕ→Atom G k}(h:0<s)(p:SumBudget (fun i=>(X i).budget s) A)(t:ℕ)(n:Side) :
    rye (seriesScore n X) (t+1)= lagoon (spreadW X (t+1)) n:=by
    funext x; let b (i:ℕ):=(X i).budget s; let C:= garden G s k (t+1)
    let L (i:ℕ×Shift (Keys t)):= flair x (coverInk (X i.1) (t+1)) i.2
    have hp:= hinge_paid (show 0<steep s from div_pos h (by norm_num)) t
    have ht i := (flair_cost (rocksA (X i) h t) (show 0<steep s from div_pos h (by norm_num)) x).unweighted hp.le
    have hz: Summable L:= by
        apply Summable.of_norm; apply (summable_prod_of_nonneg (fun i=>norm_nonneg (L i))).mpr; refine ⟨fun i=> (ht i).2.1,Summable.of_nonneg_of_le (fun i=>tsum_nonneg fun _=>norm_nonneg _) (fun i=>(ht i).2.2) ?_⟩; exact (p.2.1.mul_right C).mul_right _
    rw [← (crownS h p x).tsum_eq]; simp_rw [wraps_atom]
    unfold lagoon
    change (∑' i:ℕ,∑' w,L (i,w))=_
    let q:= Equiv.prodComm (Shift (Keys t)) ℕ
    rw [← hz.tsum_prod,← q.tsum_eq L]
    change tsum (L ∘ q)=_; rw [(q.summable_iff.mpr hz).tsum_prod]; apply tsum_congr; intro i
    by_cases hx:trope x i
    · change (∑' r,flair x (coverInk (X r) (t+1)) i)=_
      simp only [flair_hit hx]; rfl
    change (∑' r,flair x (coverInk (X r) (t+1)) i)=_
    simp [flair_miss hx]
lemma wraps_fire {P:Stack G k}(h:0<s)(hw:SumBudget (fun i=>(P i).budget s) A)(n:Side)(m t:ℕ):
    written P n m (t+1) = lagoon (fire P m (t+1)) n:=by
    by_cases H:k+1+m=t
    · subst t; have hx:k+2+m=k+1+m+1:=by omega
      rw [written, sprig,hx,shine_lit]; unfold fire; rw [hx,shine_lit]; exact wraps_series h hw _ _
    have ht:k+2+m≠t+1:=by omega
    rw [written, sprig,shine_dark ht]; unfold fire; rw [shine_dark ht,lagoon_none]

-- scalar lifted integrals unnecessary for the value-null remainder.
end YM.WilsonCoeffUV.Bank.Mosaic
