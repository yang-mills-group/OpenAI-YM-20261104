import YM.Contacts.Sentry.Stride
import YM.Contacts.Mat.Avoid
/-! Cursor locks in ANY coordinate order. Never need f.PointLimits at axis ties. -/
set_option autoImplicit false
noncomputable section
namespace YM.Contacts.Sensor
open Function Set Filter MeasureTheory Extraction Table Org Spec Power Next.UVStress Costar Mat Analysis Lattice
open scoped Topology BigOperators ContDiff
variable {α:Type*}{ι J :Type}[Fintype ι][DecidableEq ι][Fintype J] {b:ℝ}
  (x:ι→ E4)(y:J→ E4)
structure Ties (s:Finset (ι×Axis))(r:ℝ) : Prop where
    -- `s` unlocked
    theirs j i : (i,j) ∉ s → ∃ z:ℤ, x i j=r*z
    own j i k : (i,j)∉s → (k,j)∉s → i ≠ k → x i j ≠ x k j
    other j i w :(i,j)∉s→ x i j ≠ y w j
lemma Ties.from (r:ℝ) : Ties x y Finset.univ r:=⟨by simp,by simp,by simp⟩
lemma Ties.note (r:ℝ){j:ι}(h:x j=0) : Ties x (J:=Fin 0) Fin.elim0
      (Finset.univ.filter (fun i=>i.1≠j)) r:=by
    constructor
    · intro v i ht; simp only [Finset.mem_filter,Finset.mem_univ,true_and,ne_eq,not_not] at ht; rw [ht,h]; exact ⟨0,by simp⟩
    · intro v i k hi hk he; apply False.elim; apply he; apply (show i=j from (by simpa using hi)).trans; simpa using ((show k=j from (by simpa using hk)).symm)
    intro j i k; exact Fin.elim0 k
omit [DecidableEq ι] in
lemma Ties.all_clear (r:ℝ)(h:Ties x y ∅ r): clear ι x:= fun j i k H=> by by_contra hi; exact h.own j i k (by simp) (by simp) hi H
lemma Ties.full_clear (r:ℝ)(h:Ties x y ∅ r)(hy:clear J y): clear _ (y ⌢ x):=by
    intro i a b; rcases a,b with ⟨a|a,b|b⟩
    · exact fun he=> congr_arg _ (hy i he)
    · exact fun he=> (h.other i b a (by simp) he.symm).elim
    · exact fun he=> (h.other i a b (by simp) he).elim
    exact fun he=> congr_arg _ (Ties.all_clear x y r h i he)
lemma Ties.on_grid (S:Schedule)(j:ℕ)(h:Ties x y ∅ (S.a j)): ∃ z:ι→ Cover,x=S.gridPoint j ∘ z:= by
    choose z hz using fun i k=> h.theirs k i (by simp); exact ⟨z,funext fun i=> PiLp.ext fun k=> hz i k⟩

lemma Ties.successor (r:ℝ)(hp:0<r)(i:ι)(a:Axis)(n:ℕ): ∃ P : Nodes n (clusterRadius (ι⊕J) n), ∀ s:Finset (ι×Axis), (i,a)∉ s→ Ties x y (insert (i,a) s) r → ∀ j:Fin (n+1), Ties (pushed x i (r • basis a) (P.v j)) y s r:=by
    obtain ⟨p,hp'⟩:= between_avoiding (n:=n) (x i a) r hp (fun j:ι⊕J=> (x ⌢ y) j a); refine ⟨p,?_⟩
    intro s hk h j; let z:= pushed x i (r • basis a) (p.v j)
    have hx : z i a= x i a+p.v j*r:=by simp [z,pushed, basis_eq]
    have hh k l (he:(k,l)≠(i,a)): z k l=x k l:=by by_cases h:k=i; subst k; have hl:l≠a:=fun h=>he (congr_arg _ h); simp [z,pushed,hl]; simp [z,pushed,h]
    have hq k (he:k≠i): z i a ≠ z k a:=by rw [hx,hh _ _ (fun H=> he (congr_arg Prod.fst H))]; exact (hp' j).2 (Sum.inl k)
    refine { theirs:=fun l k he=>?_, own:=fun l k h' he ht hi=>?_, other:=fun l k w he=>?_ }; -- z syntax below
    · by_cases h':(k,l)=(i,a)
      · change ∃ t:ℤ,z k l=r*t; rw [show k=i from congr_arg Prod.fst h',show l=a from congr_arg Prod.snd h', hx] -- doesn't simplify?
        exact (hp' j).1
      change ∃ t:ℤ,z k l=r*t; rw [hh _ _ h']; exact h.theirs l k (by simp [he,h'])
    · change z k l ≠ z h' l; by_cases hp:(k,l)=(i,a); rw [show k=i from congr_arg Prod.fst hp,show l=a from congr_arg Prod.snd hp]; exact hq _ (by rw [← show k=i from congr_arg Prod.fst hp]; exact Ne.symm hi)
      by_cases hP:(h',l)=(i,a); rw [show h'=i from congr_arg Prod.fst hP,show l=a from congr_arg Prod.snd hP]; exact Ne.symm (hq _ (by rw [← show h'=i from congr_arg Prod.fst hP]; exact hi))
      rw [hh _ _ hp,hh _ _ hP]; exact h.own l k h' (by simp [hp,he]) (by simp [hP,ht]) hi
    change z k l≠y w l; by_cases hp:(k,l)=(i,a); rw [show k=i from congr_arg Prod.fst hp,show l=a from congr_arg Prod.snd hp,hx]; exact (hp' j).2 (Sum.inr w)
    rw [hh _ _ hp]; exact h.other l k w (by simp [hp,he])

lemma tie_grid (P:Pace α)(S:Schedule)(j:α→ℕ)(x:α→ι→ E4)(y:α→ J→ E4)(h:∀ᶠ i in P.net, Ties (x i) (y i) ∅ (S.a (j i))) : ∃ z:α→ι→ Cover,x =ᶠ[P.net] (fun i=> S.gridPoint (j i) ∘ z i):= by
   choose! f hf using fun i (hx:Ties (x i) (y i) ∅ (S.a (j i)))=> Ties.on_grid (x i) (y i) S (j i) hx; exact ⟨f,h.mono hf⟩

lemma pushed_allot (P:Pace α) (x:α→ι→ E4)(k:ι){v:α→E4}{t:α→ℝ}(ht:P.Priced 0 t)(hv:P.Priced (-b) v)(i): Allotment (fun j=> pushed (x j) k (v j) (t j) i) (fun j=> x j i) b P:=by
    by_cases h:i=k
    · subst k; simpa only [Allotment,pushed,Function.update_self, add_sub_cancel_left,zero_add] using! ht.smul hv
    simp_rw [Allotment,pushed, Function.update_of_ne h, sub_self]; apply Pace.Priced.zeros
lemma to_price {P:Pace α}(f:α→ℝ){t:ℝ}(h:∀ᶠ i in P.net, f i∈ Icc 0 t):P.Priced 0 f := Pace.Priced.from_bound t (h.mono fun i hi=>by rw [Real.norm_of_nonneg hi.1]; exact hi.2)
end YM.Contacts.Sensor
