import YM.RG12.Strike.Pool
/-! # Angular charge tested on a symmetric traceless tensor -/
set_option autoImplicit false
noncomputable section
open scoped Topology BigOperators Classical
namespace YM.RG12.Strike
open Function Set Filter MeasureTheory Finset Equiv
variable {n m d:ℕ}(L:Lay d (Berth n m)) {P:Strip n→ℂ}(hP:Cloud P)
def sibling : Equiv.Perm (Berth n m) := L.symm.trans ((prodCongr (swap false true) (Equiv.refl _)).trans L)
lemma sib1 (i) : sibling L (a L i)=b L i:=by simp [sibling,a,b]
lemma sib2 (i) : sibling L (b L i)=a L i:=by simp [sibling,a,b]
def Super (L:Lay d (Berth n m)):Prop:= ∃ k:Fin d,∃ i j:Fin n,a L k=Sum.inl i ∧ b L k= Sum.inl j
lemma charm (h:¬Super L) : ∃ f:Fin n↪Fin m,∀ i:Fin n, sibling L (Sum.inl i)=Sum.inr (f i):=by
   choose f he using show ∀ i:Fin n, ∃ k:Fin m, sibling L (Sum.inl i)=Sum.inr k from fun i=> by
      obtain ⟨⟨b₀,j⟩,hz⟩:= L.surjective (Sum.inl i)
      rw [←hz]; cases b₀
      · cases hf:sibling L (L (false,j)) with
        | inl a₀=> exact False.elim (h ⟨j,i,a₀,hz,(sib1 L j).symm.trans hf⟩)
        | _ => exact ⟨_,rfl⟩
      cases hf:sibling L (L (true,j)) with
      | inl a₀=> exact False.elim (h ⟨j,a₀,i,(sib2 L j).symm.trans hf,hz⟩)
      | _=>exact ⟨_,rfl⟩
   have hj:Function.Injective f:=fun i j he'=>Sum.inl_injective ((sibling L).injective ((he i).trans ((congr_arg Sum.inr he').trans (he j).symm))) -- missing β arg
   exact ⟨⟨f,hj⟩,he⟩
include hP
lemma past (u:Strip m)(hn:m<n): ∑ v:Strip n,P v * ∏ l:Fin d,work L v u l=0:=by
   by_cases he:Super L
   · obtain ⟨i,x,y,hE,hQ⟩:=he; exact vanishes x y L hP u i hE hQ
   obtain ⟨f,hQ⟩:= charm L he; have hm:= Fintype.card_le_of_embedding f; rw [Fintype.card_fin,Fintype.card_fin] at hm; omega
-- when each side full exactly. Then mate all. Every admitted configuration yields P u.
omit hP in
lemma port (L:Lay d (Berth m m)){P:Strip m→ℂ}(hQ:Cloud P) (u:Strip m) :
    ∑ v:Strip m, P v * ∏ l:Fin d, work L v u l=(if Super L then 0 else 1)*P u:=by
    split
    · next h=> obtain ⟨i,x,y,hE,hu⟩:=h; rw [vanishes x y L hQ u i hE hu,zero_mul]
    next he=>
      rw [one_mul]; obtain ⟨f,h⟩:=charm L he
      let e:= Equiv.ofBijective f ⟨f.injective, Finite.surjective_of_injective f.injective⟩
      let v:=u ∘ e
      rw [Finset.sum_eq_single v]
      ·
        have hw : ∀ i:Fin d,work L v u i=1:=by
           intro i; cases hx:a L i with
           | inl a₀=>
             have hb:= h a₀; rw [← hx, sib1] at hb
             unfold work; simp [hx,hb,woven,v,e,matchC]
           | inr a₀=>
             obtain ⟨b₀,hb⟩:= e.surjective a₀
             have hh:=h b₀; change e b₀=a₀ at hb; change f b₀=a₀ at hb
             rw [hb, ← hx] at hh; have hZ:b L i=Sum.inl b₀:=(sibling L).injective (by rw [hh,sib2])
             unfold work; simp [matchC,hx,hZ,woven,v,e,hb]
        simp_rw [hw,Finset.prod_const_one, mul_one]; exact hQ.symmetric e u
      · intro w _ hw; suffices hv : ∏ i,work L w u i=0 by rw [hv,mul_zero]
        obtain ⟨i,hi⟩:= Function.ne_iff.mp hw -- name
        obtain ⟨⟨b₀,k⟩,hk⟩:=L.surjective (Sum.inl i)
        refine Finset.prod_eq_zero (s:=univ) (i:=k) (mem_univ _) ?_
        cases b₀
        · change a L k =Sum.inl i at hk; have hs: b L k=Sum.inr (f i):=by rw [← sib1 L k,hk,h]
          unfold work; simp_rw [hk,hs]; exact if_neg hi
        change b L k=Sum.inl i at hk; have hs: a L k=Sum.inr (f i):=by rw [← sib2 L k,hk,h]
        unfold work; simp_rw [hk,hs]; exact if_neg (Ne.symm hi)
      simp

omit hP
-- annular integrals. Odd booking.
def rain (v:Strip n)(x:R):ℂ:=∏ i:Fin n,(x (v i):ℂ)
lemma rain_cont (v:Strip n): Continuous (rain v):=by unfold rain; fun_prop
def fall (P:Strip n→ℂ)(x:R):ℂ:=∑ v:Strip n,P v*rain v x
lemma fall_cont (P:Strip n→ℂ): Continuous (fall P):=by unfold fall rain; fun_prop
variable {w:R→ℂ}(hw:Round w)
omit L in
lemma splice (v:Strip n)(u:Strip m)(x:R)(c:ℂ):c*(∏ i:Berth n m,(x (woven v u i):ℂ))=c*rain v x*rain u x:=by rw [Fintype.prod_sum_type,mul_assoc];rfl
include hw
omit L in
lemma even {j:ℕ}(L:Lay j (Berth n m)) : ∃ c:ℂ,∀ v:Strip n,∀u:Strip m,
    (∫ x:R, w x*rain v x* rain u x)= c * ∑ L:Lay j (Berth n m),∏ k:Fin j,work L v u k:=by
    obtain ⟨c,h⟩:= coins w hw L;exact ⟨c,fun v u=> by have he := h (woven v u); simp_rw [splice] at he; exact he⟩
omit L in
lemma odd (v:Strip n)(u:Strip m)(he:Odd (n+m)): (∫ x:R,w x*rain v x*rain u x)=0:=by
    have hz:=void w hw (by simpa [Berth] using he : Odd (Fintype.card (Berth n m))) (bar ∘ woven v u)
    unfold bill at hz; simp_rw [Function.comp_apply, project,splice] at hz; exact hz
omit L in
lemma tally (P:Strip n→ℂ)(u:Strip m): (∫ x:R,w x*fall P x*rain u x) = ∑ v:Strip n,P v*(∫ x:R,w x*rain v x*rain u x):=by
   have he x: w x*fall P x*rain u x=∑ v:Strip n,P v * (w x* rain v x*rain u x):=by
      unfold fall; rw [mul_sum,sum_mul]; apply sum_congr rfl; intro i _; ring
   simp_rw [he]; rw [integral_finsetSum]
   · simp only [integral_const_mul]
   intro v _
   have hi:Integrable (fun x=> w x * (rain v x*rain u x)):=weighted w hw.toAnnular ((rain_cont v).mul (rain_cont u))
   simpa [mul_assoc] using! hi.const_mul (P v) -- simp_rw proof cause
omit L in
omit hw in
lemma stitch (h:Even (n+m)): ∃ j:ℕ, Nonempty (Lay j (Berth n m)):=by
   obtain ⟨j,hj⟩:=h
   exact ⟨j,Fintype.card_eq.mp (by simp [Berth]; omega)⟩
omit L in
include hP in
theorem below (u:Strip m) (h:m<n) : (∫ x:R,w x*fall P x*rain u x)=0:=by
   rw [tally hw]; by_cases he:Even (n+m)
   · obtain ⟨d,⟨L⟩⟩:= stitch (m:=m) he
     obtain ⟨c,hc⟩:=even hw L
     simp_rw [hc,mul_left_comm (P _) c, ← mul_sum _ _ c, mul_sum _ _ (P _)]
     rw [sum_comm]; simp_rw [past (n:=n) _ hP u h]; simp
   have hh: Odd (n+m):=Nat.not_even_iff_odd.mp he
   simp_rw [odd hw _ u hh]; simp
omit L in
/-- Moment at matching degree, constant independent of tensor and axes. -/
theorem closure : ∃ c:ℂ, ∀ P:Strip n→ℂ,Cloud P→∀ u:Strip n, (∫ x:R,w x*fall P x*rain u x)=c*P u:=by
   obtain ⟨d,⟨L⟩⟩:=stitch (n:=n) (m:=n) ⟨n,rfl⟩; obtain ⟨c,hc⟩:= even hw L
   refine ⟨c*(∑ L:Lay d (Berth n n), if Super L then 0 else 1),fun P hP u=>?_⟩
   rw [tally hw]; simp_rw [hc,mul_left_comm (P _) c, ← mul_sum _ _ c, mul_sum _ _ (P _)]
   rw [sum_comm,mul_assoc,Finset.sum_mul]
   exact congr_arg _ (sum_congr rfl fun L _=> port L hP u)
end YM.RG12.Strike
