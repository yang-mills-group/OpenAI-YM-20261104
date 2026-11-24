import YM.XSpace.Sleigh

/-!
# Periodic first-order unconditioning: quant estimate

Calculate the finite localized X-space diagrams via the infinite cover Feynman-gauge lines,
including the noncompact sum over virtual cubic plaquettes. This estimate handles *only*
the image/periodic corrections, so allow arbitrary dependencies on the finite family of fields
but UNIFORM over all R & tested positions (price in terms of the specified inequalities).
No UV counterterms in this estimate (see later; may buy all powers here first).
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Comets
open Function Set Filter Lattice RG Wilson Source Source.Drops Next.Rank.Normal Contraction Chart2 JetGauge Outline Outline.Given
open Sail (reach)
open scoped Topology BigOperators
variable {G:Gauge} {R:Period} {Z:Type*} {p : Music (Z:=Z) (G:=G)}

def drip (o:Cover)(m:ℕ): Finset Cover := (box m).map (Equiv.addRight o).toEmbedding
lemma mem_drip (o:Cover)(m:ℕ)(x:Cover): x∈drip o m ↔ reach (x-o) ≤ m:= by rw [drip,Finset.mem_map_equiv]; change x-o∈box m ↔ _; apply Sail.box_rate
lemma num_drip (o: Cover)(m:ℕ): (drip o m).card=(2*m+1)^4:=by rw [drip, Finset.card_map, Sail.volume_box]

def pool (R:Period) (o:Cover)(m:ℕ): Finset R.Sites:= (drip o m).image (wrap R.side)
lemma mem_pool (o:Cover)(m:ℕ)(x:R.Sites): x∈pool R o m ↔ pdist (x-wrap R.side o) ≤ m:= by
  rw [pool,Finset.mem_image]; refine ⟨?_,fun h=>?_⟩; rintro ⟨y,hy,rfl⟩; rw [← map_sub]; exact (pc_cast ..).trans ((mem_drip ..).1 hy)
  refine ⟨lift (x-wrap R.side o)+o,(mem_drip ..).2 (by rw [add_sub_cancel_right]; exact h),?_⟩; rw [map_add,wrap_lift,sub_add_cancel]
lemma drip_inj (R:Period)(o:Cover)(m:ℕ)(h:2*m<R.side.val) {x y:Cover}(hx:x∈drip o m)(hy:y∈drip o m)(he:wrap R.side x=wrap R.side y): x=y:=by
  have hp (x:Cover) (hx:x∈drip o m): lift (wrap R.side (x-o))=x-o:= lift_eq_iff.mpr ⟨rfl,fun j=> by have hp: ((x-o) j).natAbs ≤ m:=(Sail.reach_at ..).trans ((mem_drip ..).1 hx); omega⟩
  suffices x-o=y-o by exact sub_left_inj.mp this
  rw [← hp x hx, ← hp y hy, map_sub, map_sub, he]

def snow (q:PlaqAxes)(x:R.Sites):= (R.reflectedFace (x,q)).1
lemma snow_step (q:PlaqAxes)(x:R.Sites): separation (-x) (snow (R:=R) q x) ≤ 2 :=by
  let A:= -x-step q.val.1; let y:= A-step q.val.2; change separation (-x) y≤2
  have h:A+step q.val.1= -x:=sub_add_cancel ..; have ht:y+step q.val.2 = A:= sub_add_cancel ..
  apply le_trans (separation_triangle (-x) A y)
  have he := Work.E01.sep_step_le A q.val.1; rw [h, separation_comm] at he
  have hx:= Work.E01.sep_step_le y q.val.2; rw [ht,separation_comm] at hx; omega
lemma snow_invol (q:PlaqAxes): Function.Involutive (snow (R:=R) q):=fun x=> congr_arg Prod.fst (R.face_invol (x,q))
abbrev heavy (r:ℕ):= 3*(r+1)
lemma frozen {m:ℕ}(o:Cover)(q:PlaqAxes)(h:Tall R o)(hp:512*(1+m)≤ R.side.val):
    Disjoint (pool R o (heavy m)) ((pool R o (heavy m)).image (snow (R:=R) q)):=by
  refine Finset.disjoint_left.mpr fun x hx hy=> ?_; obtain ⟨y,hY,rfl⟩:= Finset.mem_image.mp hy; let a:= wrap R.side o
  have he : separation a (-y) ≤ heavy m+2:= (separation_triangle a (snow (R:=R) q y) (-y)).trans (add_le_add (by rw [separation_comm]; exact (mem_pool ..).1 hx) (by rw [separation_comm]; exact snow_step (R:=R) ..))
  have hb : separation (-y) (-a) ≤ heavy m:=by rw [separation,show -y- -a= -(y-a) by abel,pdist_neg]; exact (mem_pool ..).1 hY
  have H : R.side.val ≤16*separation a (-a):=by rw [separation,sub_neg_eq_add]; unfold a; rw [← map_add]; exact h
  have ht:=separation_triangle a (-y) (-a); unfold heavy at *; omega

-- tails get no tests on free reconstruction (layout shifts & cubature track)
def allowance (R:Period)(r:ℕ):ℝ:= saving r + (1+(r:ℝ))^5 / R.side.val
lemma allowance_pos (R:Period)(r:ℕ):0<allowance R r:=by unfold allowance; positivity [saving_ok r,Bloch.side_pos R.side]
lemma permit (R:Period)(r:ℕ): budget R r ≤ allowance R r:=by unfold allowance; apply le_trans _ (le_add_of_nonneg_left (saving_ok r).le); unfold budget; gcongr; apply le_self_pow₀ (by simp) (by decide)

private lemma ignores (o: Cover)(q:PlaqAxes) (r:ℕ)(x: Z→Cover)(h:∀ i,reach (x i-o)≤r) (y:R.Sites) (hy:y∉pool R o (heavy r))
    (hy': y∉(pool R o (heavy r)).image (snow (R:=R) q)) (i:Z): (dawn G R).goal r (wrap R.side (x i)) y:=by
  let a:=wrap R.side o; let b:=snow (R:=R) q y; let x':=wrap R.side (x i)
  have he : separation x' a ≤ r :=by unfold x' a separation; rw [← map_sub]; exact (pc_cast ..).trans (h i)
  have hv : b ∉ pool R o (heavy r):=fun hh=>hy' (Finset.mem_image.mpr ⟨b,hh,snow_invol (R:=R) q y⟩)
  have hs: heavy r< separation y a:=lt_of_not_ge (mt (mem_pool ..).2 hy); have hs':heavy r < separation b a:=lt_of_not_ge (mt (mem_pool ..).2 hv)
  change r≤ separation x' y∧r≤ separation x' (-y); have ha : separation b (-y) ≤2:= separation_comm .. ▸ snow_step (R:=R) q y
  have hp:=separation_triangle y x' a; have hi:=separation_triangle (-y) x' a; have hh:= separation_triangle b (-y) a; rw [separation_comm y x'] at hp; rw [separation_comm (-y) x'] at hi; unfold heavy at *; omega
private lemma forbids (o:Cover)(r:ℕ)(x:Z→Cover) (h:∀ i,reach (x i-o)≤r) (y:Cover)(hy:y∉drip o (heavy r))(i:Z): (dusk G).goal r (x i) y:=by
  have he : heavy r < reach (y-o):=lt_of_not_ge (mt (mem_drip ..).2 hy)
  have hh : reach (y-o) ≤ reach (x i-y)+ r:=by rw [show y-o= -(x i-y)+(x i-o) by abel]; apply (Sail.tree ..).trans; rw [Sail.reach_neg]; exact add_le_add (_root_.le_refl _) (h i)
  change r≤ reach (x i-y); unfold heavy at he; omega

-- estimates usable in assembling all terms at this first order

def interact (q:PlaqAxes)(R:Period)(x: Z→R.Sites)(p:Music (G:=G) (Z:=Z)):= (2:ℂ)⁻¹ * ∑ y:R.Sites,witness (y,q) (dawn G R) x p
def bulk (q:PlaqAxes)(x:Z→Cover)(p:Music (G:=G) (Z:=Z)):= ∑' y:Cover, witness (y,q) (dusk G) x p
set_option maxHeartbeats 900000 in
lemma interaction_price (p:Music (Z:=Z) (G:=G)) (q:PlaqAxes): ∃ A:ℝ,0≤A∧∀ R: Period,∀ o:Cover,Tall R o →∀ r:ℕ,512*(1+r)≤ R.side.val →∀ z:Z→Cover,(∀ i,reach (z i-o)≤ r)→ ‖interact q R (wrap R.side ∘ z) p-bulk q z p‖≤ A*allowance R r:=by
  obtain ⟨C,hC,H⟩:= witness_quotation q p; obtain ⟨B,hB,K⟩:=toll_integrals (night G) p q; obtain ⟨D,hD,L⟩:= toll_integrals (dawning G) p q; refine ⟨C*4* (7:ℝ)^4+B+D,by positivity,?_⟩
  intro R o ho r hr z hz; let m:=heavy r; let b:=pool R o m; let t:=b ∪ b.image (snow (R:=R) q); let c:=drip o m; let w:=wrap R.side; set M:=w ∘ z
  let f y:= witness (y,q) (dawn G R) M p; let g y:= witness (y,q) (dusk G) z p
  have he : (∑ i∈t, f i)= 2* ∑ i∈b, f i:=by
    rw [Finset.sum_union (show Disjoint b (b.image (snow (R:=R) q)) from frozen o q ho hr), Finset.sum_image, two_mul]
    · apply congr_arg ((∑ i∈b, f i)+ ·); have h (i: R.Sites) : f (snow (R:=R) q i)=f i:= (reflection (R:=R) (i,q) M p).symm
      simp_rw [h] 
    exact fun i _ j _ h=> (snow_invol (R:=R) q).injective h
  have hp : (∑ i∈b,f i)=∑ i∈c,f (w i):= Finset.sum_image (fun _ (h: _∈c) _ (H:_∈c)=> drip_inj R o m (by unfold m heavy; omega) h H)
  have hh : interact q R (w ∘ z) p=(∑ i∈c, f (w i))+(2:ℂ)⁻¹ * ∑ i ∈ tᶜ,f i:=by unfold interact; change (2:ℂ)⁻¹ * ∑ i, f i=_; rw [← Finset.sum_add_sum_compl t,he,hp]; ring
  let V: Set Cover:= (c : Set Cover)ᶜ; have hk: Summable g := full_cover ..
  have HB: bulk q z p=(∑ i∈c,g i)+∑' i: V,g i:= (hk.sum_add_tsum_subtype_compl c).symm
  have HD: ‖∑ i∈tᶜ,f i‖ ≤ D*saving r:=by apply (norm_sum_le ..).trans; apply L R r M tᶜ; intro y hy i; rw [Finset.mem_compl] at hy; simp only [t,Finset.mem_union, not_or] at hy; exact ignores o q r z hz y hy.1 hy.2 i
  have HU: ‖∑' i:V,g i‖ ≤ B*saving r:=by
    have he : Summable fun x:V => ‖g x‖ := hk.norm.subtype _
    apply (norm_tsum_le_tsum_norm he).trans; apply he.tsum_le_of_sum_le; intro s
    rw [← Finset.sum_image (g:=Subtype.val) (f:=fun i=> ‖g i‖)]; apply K () r z; rintro y hy i
    obtain ⟨⟨y,hY⟩,hz',rfl⟩:= Finset.mem_image.mp hy; exact forbids o r z hz y hY i
    exact fun _ _ _ _ h=> Subtype.val_injective h
  set A:ℝ:=(1+(r:ℝ))^5/R.side.val; have ha:=Bloch.side_pos R.side
  have hf : ‖(∑ i∈c, f (w i))-∑ i∈c,g i‖≤ C*4*7^4*A:=by
    rw [← Finset.sum_sub_distrib]; apply (norm_sum_le ..).trans; apply le_trans (Finset.sum_le_sum (g:=fun _=> C*budget R m) fun i hi=> H R o ho m z (fun i=>(hz i).trans (by unfold m heavy; omega)) i ((mem_drip ..).1 hi)); rw [Finset.sum_const,nsmul_eq_mul, show c.card=_ from num_drip ..]
    unfold A budget; generalize g:m=m' -- unroll
    subst m'; unfold m heavy; push_cast; field_simp; rw [← sub_nonneg]; ring_nf; positivity
  let a:= ∑ i∈c,f (w i); let a':=(∑ i∈c,g i); let b':=(2:ℂ)⁻¹ *∑ i∈tᶜ,f i; let c':= (∑' i:V,g i)
  rw [hh,HB]; change ‖a+b'-(a'+c')‖ ≤ _; rw [show a+b'-(a'+c')=(a-a')+(b'-c') by abel]
  have hg : ‖b'‖ ≤ D*saving r:=by unfold b'; rw [norm_mul, norm_inv]; norm_num; apply le_trans _ HD; apply mul_le_of_le_one_left (norm_nonneg _) (by norm_num)
  apply (norm_add_le ..).trans; apply le_trans (add_le_add hf ((norm_sub_le ..).trans (add_le_add hg HU))); change C*_ *7^4*A+_≤_ * (saving r + A); have hv:0<saving r:=saving_ok _; have H0 : 0<A :=by unfold A; positivity
  rw [← sub_nonneg]; ring_nf; positivity
end YM.XSpace.Comets
