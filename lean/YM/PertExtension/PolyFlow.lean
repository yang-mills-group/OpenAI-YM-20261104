import YM.Next.RANK.Guard

/-! Local asymptotic calculus: varying polynomials in an infinite key space,
         but finite common monomial support at each use. -/
set_option autoImplicit false
set_option maxHeartbeats 1350000
noncomputable section
namespace YM.PertExtension.PolyFlow
open Function Filter Set Finset MvPolynomial Next.Rank Next.Rank.Normal
open scoped Topology Classical BigOperators
variable {ι V W U : Type*}{l : Filter ι}
structure Limit (f:ι→poly V)(p:poly V)(l:Filter ι) : Prop where
    fence : ∃ s:Finset (V→₀ℕ),p.support⊆s ∧ ∀ᶠ k in l,(f k).support⊆s
    leaves i:Tendsto (fun k=>coeff i (f k)) l (𝓝 (coeff i p))
structure Close (f:ι→poly V)(p:poly V)(m : ι→ℂ)(l:Filter ι) : Prop extends Limit f p l where
    diff : Limit (fun k:ι=>m k • (f k-p)) (0:poly V) l
def rate_as (f:ι→ℂ)(p:ℂ)(m:ι→ℂ)(l:Filter ι):= Tendsto f l (𝓝 p) ∧ Tendsto (fun k=>m k*(f k-p)) l (𝓝 0)
variable {m : ι→ℂ}{f g f' g':ι→poly V}{p q:poly V}{a b:ℂ}
lemma Limit.const : Limit (fun _=>p) p l:=⟨⟨p.support,by simp⟩,fun i=>tendsto_const_nhds⟩
lemma Close.const : Close (fun _=>p) p m l:=⟨Limit.const,by simp [Limit.const]⟩
lemma Limit.replace (h:Limit f p l)(he:f=ᶠ[l] f'): Limit f' p l := by
   obtain ⟨⟨s,hp,hw⟩,H⟩:=h
   exact ⟨⟨s,hp, (hw.and he).mono fun k hk=> by simpa only [← hk.2] using hk.1⟩,fun i=>(H i).congr' (he.mono fun k hk=> congr_arg _ hk)⟩
lemma Close.replace (h:Close f p m l)(he:f=ᶠ[l] f'): Close f' p m l := ⟨h.toLimit.replace he,h.diff.replace <| he.mono fun _ h=>by dsimp only; rw [h]⟩
lemma Limit.add (h:Limit f p l)(h':Limit g q l):Limit (f+g) (p+q) l := by
   obtain ⟨⟨s,hp,hw⟩,H⟩:=h
   obtain ⟨⟨t,hq,hv⟩,J⟩:=h'
   refine ⟨⟨s∪t,support_add.trans (union_subset_union hp hq),?_⟩,fun i=>?_⟩
   · exact (hw.and hv).mono fun k hk => support_add.trans (union_subset_union hk.1 hk.2)
   simpa using! (H i).add (J i)
lemma Limit.scale {c : ι→ℂ}(h:Limit f p l)(hc:Tendsto c l (𝓝 a)): Limit (fun k=>c k • (f k)) (a • p) l:=by
   have hu : ∀ b:ℂ,∀ q:poly V,(b • q).support ⊆ q.support:= by
     intro b z i hi ; rw [mem_support_iff, coeff_smul,smul_eq_mul] at hi;exact mem_support_iff.mpr (right_ne_zero_of_mul hi)
   obtain ⟨⟨s,hp,hw⟩,H⟩:=h
   exact ⟨⟨s,(hu _ _).trans hp,hw.mono fun _ hk=>(hu _ _).trans hk⟩,fun i=> by simpa [coeff_smul] using! hc.smul (H i)⟩
protected lemma Limit.neg (h:Limit f p l):Limit (-f) (-p) l:= by simpa only [neg_smul,one_smul] using! h.scale (tendsto_const_nhds (x:=-(1:ℂ)) (f:=l))
protected lemma Limit.sum {f:W→ι→poly V}{q:W→poly V}{s:Finset W}(h:∀ i∈s,Limit (f i) (q i) l):Limit (∑ i∈s,f i) (∑ i∈s,q i) l := by
  induction s using Finset.induction_on with
  | empty=>simpa only [Finset.sum_empty] using! (Limit.const (ι:=ι) (p:=(0:poly V)) (l:=l))
  | @insert i s hi ih=> rw [sum_insert hi,sum_insert hi]; exact (h i (by simp)).add (ih (fun i hi=>h _ (by simp [hi])))

lemma terms {p:poly V}{s:Finset (V→₀ℕ)}(h:p.support⊆s): p=∑ j∈s, (coeff j p) • (monomial j 1):=by
   have he (j:V→₀ℕ): coeff j p • monomial j 1=monomial j (coeff j p) :=by rw [←map_smul,smul_eq_mul,mul_one]
   simp_rw [he];conv_lhs => rw [p.as_sum]
   exact sum_subset h (fun i hi hh=>by rw [notMem_support_iff.mp hh,map_zero])

protected lemma Limit.operator {R:ι→poly V →ₗ[ℂ] poly W}{T:poly V →ₗ[ℂ] poly W}(hp:Limit f p l)(ht:∀ q:poly V,Limit (fun k=>R k q) (T q) l) : Limit (fun k=>R k (f k)) (T p) l :=by
  obtain ⟨s,hq,hh⟩:=hp.fence
  let Q (i:V→₀ℕ):poly V:=monomial i 1
  let g (i:V→₀ℕ) k:=coeff i (f k) • R k (Q i)
  let w i:=coeff i p • T (Q i)
  have hd j : Limit (g j) (w j) l:= (ht _).scale (hp.leaves j)
  have he : Limit (∑ i∈s,g i) (∑ i∈s,w i) l:= .sum fun j _=>hd j
  have hr:T p=∑ i∈s,w i:= by conv_lhs => rw [terms hq,map_sum];simp [w,Q]
  rw [hr];refine he.replace (hh.mono fun k hk=>?_); conv_rhs => dsimp only; rw [terms hk]
  rw [map_sum]; simp [w,Q,g]
protected lemma Limit.mul' (hf:Limit f p l)(hg:Limit g q l):Limit (fun k=>f k*g k) (p*q) l:=by
  apply hf.operator (R:=fun k=>LinearMap.mulRight ℂ (g k)) (T:=LinearMap.mulRight ℂ q)
  intro r; apply hg.operator (T:=LinearMap.mulLeft ℂ r) (R:=fun k=>LinearMap.mulLeft ℂ r) (fun _=>by exact Limit.const)

lemma Close.add (h:Close f p m l)(h':Close g q m l):Close (f+g) (p+q) m l := by
   refine ⟨h.toLimit.add h'.toLimit,?_⟩
   convert h.diff.add h'.diff using 1
   · ext k; dsimp only [Pi.add_apply]; rw [add_sub_add_comm,smul_add]
   simp
lemma Close.scale {c:ι→ℂ}(h:Close f p m l)(hy:rate_as c a m l) : Close (fun k=>c k • f k) (a•p) m l := by
  obtain ⟨hc,ht⟩:=hy
  refine ⟨h.toLimit.scale hc,?_⟩
  have he (k:ι): m k • (c k • f k-a • p)=(m k*(c k-a)) • f k + a • (m k • (f k-p)):=by simp [smul_sub, mul_smul]; module
  convert (h.toLimit.scale ht).add (h.diff.scale (tendsto_const_nhds (x:=a))) using 1
  · ext k : 1;exact he _
  simp
protected lemma Close.neg (h:Close f p m l):Close (-f) (-p) m l:=by
  refine ⟨h.toLimit.neg,?_⟩
  convert h.diff.neg using 1
  · ext1 i;dsimp only [Pi.neg_apply]; module
  simp
protected lemma Close.sum {f:W→ι→poly V}{q:W→poly V}{s:Finset W}(h:∀ i∈s,Close (f i) (q i) m l):Close (∑ i∈s,f i) (∑ i∈s,q i) m l := by
  induction s using Finset.induction_on with
  | empty=>simpa only [Finset.sum_empty] using! (Close.const (ι:=ι) (p:=(0:poly V)) (l:=l) (m:=m))
  | @insert i s hi ih=> rw [sum_insert hi,sum_insert hi]; exact (h i (by simp)).add (ih (fun i hi=>h _ (by simp [hi])))
protected lemma Close.operator {R:ι→poly V →ₗ[ℂ] poly W}{T:poly V →ₗ[ℂ] poly W}(hp:Close f p m l)(ht:∀ q:poly V,Close (fun k=>R k q) (T q) m l) : Close (fun k=>R k (f k)) (T p) m l :=by
  obtain ⟨s,hq,hh⟩:=hp.fence
  let Q (i:V→₀ℕ):poly V:=monomial i 1
  let g (i:V→₀ℕ) k:=coeff i (f k) • R k (Q i)
  let w i:=coeff i p • T (Q i)
  have hd j : Close (g j) (w j) m l:= (ht _).scale ⟨hp.toLimit.leaves j, by simpa [coeff_smul,smul_eq_mul] using hp.diff.leaves j⟩
  have he : Close (∑ i∈s,g i) (∑ i∈s,w i) m l:= .sum fun j _=>hd j
  have hr:T p=∑ i∈s,w i:= by conv_lhs => rw [terms hq,map_sum];simp [w,Q]
  rw [hr];refine he.replace (hh.mono fun k hk=>?_); conv_rhs => dsimp only; rw [terms hk]
  rw [map_sum]; simp [w,Q,g]
protected lemma Close.mul' (hf:Close f p m l)(hg:Close g q m l):Close (fun k=>f k*g k) (p*q) m l:=by
  apply hf.operator (R:=fun k=>LinearMap.mulRight ℂ (g k)) (T:=LinearMap.mulRight ℂ q)
  intro r; apply hg.operator (T:=LinearMap.mulLeft ℂ r) (R:=fun k=>LinearMap.mulLeft ℂ r) (fun _=>by exact Close.const)

end YM.PertExtension.PolyFlow
