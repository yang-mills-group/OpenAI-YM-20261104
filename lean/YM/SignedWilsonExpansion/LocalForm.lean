import YM.SignedWilsonExpansion.MarkRows
import YangMills.WilsonProof.NativeSupport.YM.MS.Theater.DataK
namespace YM.SignedWilsonExpansion.LocalForm
set_option autoImplicit false
noncomputable section
open Function Set Filter Finset
open MS MS.Menus MS.Local.Physical MS.Land MS.Book MS.Landau MS.Landau.Detect MS.Koszul MS.Plane MS.Plane.Flux MS.High MS.Plane.Domain MS.Plane.Wire MS.Pearl MS.Emit MS.Garment MS.Heat MS.Rock.Path MS.Rake
open HighRank HighScale TreeLine TreeView
open scoped Classical Topology ContDiff BigOperators
variable {G:Gauge} {r:ℕ} {u q:ℤ} {F H: Law G} {b: Bool}
lemma masked (X: Reading G)(h:Static X r u b)(t:Clock ℝ) : Form (Book.mask r (X t)) wfield u b:= by
  intro E _ _ w hw; by_cases he:w.length=r
  · rw [show fieldVal (Book.mask r (X t)) w=fieldVal (X t) w from funext fun x=> Book.enough _ (show ((sail w x).length:ℤ)=r from by rw [sail_len,he])]
    exact h.form t.1 t.2 w hw he
  rw [show fieldVal (Book.mask r (X t)) w=0 from funext fun x=> Book.strange _ (show ((sail w x).length:ℤ) ≠ r from by rw [sail_len];omega)]
  exact form_zero _

lemma mask_rank : Ranked b r (Book.mask r F):= fun w _ h=> Book.strange _ (by omega)
lemma constant_cut (r : ℤ)(g:G.El) : Book.mask r (MS.Color.repeatC g F) = MS.Color.repeatC g (Book.mask r F) :=by rw [←Garment.brush g]; exact (Garment.beam_mask (m:=0) ..).symm
lemma solid_level (H:Solid b F q) (i:ℤ): Solid b (Book.mask i F) q:= by
  refine ⟨fun l x y r h=> ?_,fun w h hx=>?_,fun w h g=> ?_,fun w h=> ?_⟩
  · by_cases ht: ((l++x::y::r).length:ℤ)=i
    · rw [Book.enough _ ht, Book.enough _ (by simpa using ht)]; exact H.symm l x y r h
    rw [Book.strange _ ht, Book.strange _ (by simpa using ht), mul_zero]
  · by_cases ht:(w.length:ℤ)=i; exacts [(Book.enough _ ht).trans (H.ghost w h hx), Book.strange _ ht]
  · change Color.repeatC g (mask i F) w=_; rw [←constant_cut]; by_cases ht:(w.length:ℤ)=i; rw [Book.enough _ ht,Book.enough _ ht];exact H.color w h g; rw [Book.strange _ ht,Book.strange _ ht]
  by_cases ht:(w.length:ℤ)=i; rw [Book.enough _ (by simpa [invertMom] using ht),Book.enough _ ht]; exact H.real' w h; rw [Book.strange _ (by simpa [invertMom] using ht),Book.strange _ ht,star_zero]
lemma solid_limit (A : ℝ→ Law G)(h:∀ i,Solid false (A i) q)(p:∀ w,Tendsto (fun x=> A x w) atBot (𝓝 (F w))) : Solid false F q:= by
  refine ⟨fun l i k r _=>?_,fun w he hv=> ?_,fun w hc a=> ?_,fun w he=>?_⟩
  · have hx t:= (h t).symm l i k r (fun a=>Bool.noConfusion a)
    exact tendsto_nhds_unique ((p _).congr hx) ((p _).const_mul _)
  · have hx t:= (h t).ghost w he hv
    exact tendsto_nhds_unique ((p _).congr hx) tendsto_const_nhds
  · have hv: Tendsto (fun x=> solo a w (A x)) atBot (𝓝 (solo a w F)):= by
      clear h hc; induction w generalizing F A with
      | nil=> exact p _
      | cons i w ih=> obtain ⟨⟨j,k⟩,q⟩:=i; exact tendsto_finsetSum Finset.univ fun z _=> (ih (A:=fun x l=>A x (((j,z),q)::l)) (fun i=> p _)).const_mul _
    exact tendsto_nhds_unique (hv.congr fun x=>(h x).color w hc a) (p _)
  have hx i:= (h i).real' w he; exact tendsto_nhds_unique ((p _).congr hx) (p w|>.star)

lemma height_rank (d:Labels.Key G→₀ℕ): 2*(Finsupp.weight Labels.bidegree d).2 ≤ (Finsupp.weight Labels.bidegree d).1:= by
  rw [Labels.weight_slot]; change 2*d.sum (fun _ k=>k)≤Labels.height d
  unfold Labels.height; rw [Finsupp.weight_apply]; unfold Finsupp.sum; rw [Finset.mul_sum]; refine Finset.sum_le_sum fun i _=>?_; change _≤d i *Labels.generation i; rw [mul_comm]; exact Nat.mul_le_mul_left _ (by unfold Labels.generation; omega)
lemma gone3 : Allowed G 4 3=⊥:= by
  apply bot_unique; intro F h; obtain ⟨p,hp,rfl⟩:= Theater.chooseX (G:=G) (r:=3) (h:=4) h
  have hz:p=0:= by
    by_contra! ne; obtain ⟨i,hi⟩:= MvPolynomial.exists_coeff_ne_zero ne; have ht:= (Theater.nodeId _ _).mp ((Theater.cinema _).mp hp|>.1) hi; have he:= height_rank i; rw [ht] at he; norm_num at he
  rw [hz,map_zero]; exact Submodule.zero_mem _

lemma gone_neg : Lease G (4-1) 3 (-1)=⊥:= by
  apply bot_unique; intro F h; obtain ⟨ht,hx,hp⟩:= lease_one.mp h
  apply (Submodule.mem_bot _).mpr; funext w
  have c:Course false w:=fun t=> Bool.noConfusion t
  by_cases he:w.length=3
  · by_cases hi: (4:ℤ)-1<fieldDim wfield w; · exact hx.no_tall w c hi
    refine ht.ghost w c ?_; have hb:= length_pay w; have H:=pay_eq w (by omega)
    have hh:0≤fieldDim ghostNo w:=by unfold fieldDim; apply List.sum_nonneg; intro i hv; obtain ⟨u,hu,rfl⟩:=List.mem_map.mp hv; exact role_no u (H u hu)
    omega
  exact hp w c he
lemma cubic_free (h:F∈Lease G 4 3 0)(hr:natQ F=0): F=0:= by
  have ht:= exacts h hr; rw [gone3,gone_neg,Submodule.map_bot,sup_bot_eq] at ht; exact (Submodule.mem_bot _).mp ht
end
end YM.SignedWilsonExpansion.LocalForm
