import YM.FVA2.O.Ward.Atoms
/-!
# Singlet Slavnov and evolution
Sign `q→q+1` for J. Sym/color/reality work without assuming off-chart momenta zero.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Ward
open MS Function Filter Set Finset MS.Plane MS.Koszul Flux MeasureTheory MS.Heat MS.Book Convolve Signal
open MS.Breeze MS.Latch MS.Native MS.Osc.Snap MS.Osc MS.Fiddle MS.Garment MS.Garment.Wick MS.Rock MS.Rock.Path MS.City MS.Rake MS.Tone Momentum MS.Landau Detect MS.Color
open MS.Land MS.Outlook MS.Local.Physical
variable {G:Gauge}{U: Edge G}{F H: T (Law G)}{v w:Law G}{y s:ℝ}{n:ℕ}{q r t:ℤ}{b:Bool}
abbrev vid (U:Edge G)(t:ℤ): Prop:= ∀ i j p,U i j p≠0→ ghostNo i+ghostNo j= -t
lemma tax (h:vid U t)(hf:Solid false v q)(l: List (Lane4 G))(p)(hl:fieldDim ghostNo l ≠ q+t): trc U p v l=0:= by
    rw [at_trc]; refine Finset.sum_eq_zero (fun a _=> Finset.sum_eq_zero fun b _=>?_); by_cases he:U a b p=0; rw [he,zero_mul]; obtain hp:=h _ _ _ he; rw [hf.ghost _ (fun i=>Bool.noConfusion i) ?_, mul_zero]; simp only [field_cons]; omega
lemma widthQ (i j: BH G)(p): ( Wick.Q G 0 ).table i j p≠0→ ghostNo i-ghostNo j=1 := by
    contrapose!; intro h; unfold Wick.Q Landau.send; dsimp only; unfold Landau.choir; split; swap; rfl
    rcases i with ⟨⟨_|i,_|_⟩,a⟩ <;> rcases j with ⟨⟨_|j,_|_⟩,b⟩ <;> norm_num [ghostNo,ghostChannel] at h <;> rfl
lemma ascent (he:Solid false v q): Solid false ((Wick.Q G 0).raise v) (q+1):= by
    obtain ⟨H,ht⟩:= (Local.Physical.room _ _).mp he; refine ( Local.Physical.room _ _ ).mpr ⟨ ⟨ ( Wick.Q G 0).move.sym (clayS he),?_,?_⟩,?_⟩; · intro k; change repeatC k ((send id).raise v)=_; rw [ commute, H.color ]; rfl
    · change overC ((send id).raise v)=_; rw [ over_act id (fun _=>rfl), H.shadow ]; rfl
    intro u hu; rw [visit_Z,← visit_zero (R:=ℂ) (b:=true) (p:=Landau.parity) u]; apply visit_agree; intro a i k hv; apply Finset.sum_eq_zero; intro j _; by_cases hh:( Wick.Q G 0).table i.1 j i.2=0; · rw [hh,zero_mul];
    obtain hQ:= widthQ _ _ _ hh; rw [ht _ ?_,mul_zero]; rw [visit_field,hv]; omega
lemma ink (hp:Solid false v t): ∀ g:G.El, repeatC g v=v := ((Local.Physical.room _ _).mp hp).1.color
lemma loopC (h:vid U t)(hm:Rolled U)(hk: RealF U)(hs:∃ K:YMflow Axis, U=Landau.choir K id)(hv:Solid false v q)(hp:v∈Wallet G): Solid false (orbit U planeF v) (q+t):= by
    obtain ⟨K,rfl⟩:= hs; obtain hM:= hm.pays Geo.Coherent hp; rw [finite_cc planeF hM]; let L:Edge G:= Landau.choir K id
    refine ⟨fun l i j k _=> Wind.Modeled.lap_symm planeF (clayS hv) l i j k, fun l _ hx=>?_,?_,?_⟩
    · unfold Ccy; simp_rw [tax h hv l _ hx]; simp
    · intro l _ g; change repeatC g _ l= _; rw [cycle_dye K id g planeF hM,ink hv g]
    intro l _; unfold Ccy; rw [← integral_neg_eq_self (μ:=planeF) (fun p=> trc L p v (invertMom l)) ]; unfold L; simp_rw [inv_trc (fun l=> hv.real' _ (fun _i=>Bool.noConfusion _i)) hk]; exact integral_conj
lemma treeC (h:vid U t)(hm:closed U Landau.parity b)(hr:Reverse U Landau.parity)(hk: RealF U)(hs:∃ K:YMflow Axis,U= Landau.choir K id)(hx:Solid false v q)(hy:Solid false w r): Solid false (boulevard Landau.parity U v w) (q+r+t) := by
    obtain ⟨K,rfl⟩:= hs; rw [blvd]; let L: Edge G:= Landau.choir K id
    refine ⟨ fun l i j k _=> tree_sym hm (clayS hx) (clayS hy) l i j k, fun l _ hu=>?_, ?_, fun l _=> globe (fun l=>hx.real' _ (fun i=>Bool.noConfusion i)) (fun l=> hy.real' _ (fun i=>Bool.noConfusion i)) hk hr l⟩
    · unfold tree; rw [scatter_congr _ _ _ (fun _ _=>(0:ℂ)) ?_]; exact map_zero (allocate ..)
      intro a b hp; rw [convertR hr]; refine Finset.sum_eq_zero (fun i _=> Finset.sum_eq_zero fun j _=>?_); unfold radius; dsimp only; by_cases he: ( Landau.choir K id ) i j (-net a)=0; simp only [he]; ring; obtain hk:= h _ _ _ he
      let Y (l:List (Lane4 G)):=fieldDim ghostNo l; have hz:Y a+Y b=Y l:= split_sum _ hp;
      by_cases hd:ghostNo i+ Y a=q; swap; · rw [hx.ghost _ (fun i=> Bool.noConfusion i) (field_cons _ _ _ ▸ hd) ]; ring
      rw [hy.ghost _ (fun i=>Bool.noConfusion i) ?_, mul_zero]; rw [field_cons]; unfold Y at hz hd; intro hn; apply hu; dsimp only at hn; rw [← hz,← hd,← hn]; omega
    intro l _ g; change repeatC g _ l=_; rw [tree_dye K id g hm,ink hx,ink hy]
lemma sA (hx:Solid false v q)(hv:v∈Wallet G): Solid false ((Φ G s).P v) q := by
    obtain he:= loopC (U:=A0 G s 0) (t:=0) (kred G s 0) rA (voile_a G s 0) ⟨_,rfl⟩ hx hv; rw [add_zero] at he; exact he
lemma sB (hx:Solid false v q)(hv:v∈ Wallet G): Solid false ((Φ G s).J v) (q+1):= by
    have he: Credit 1 (B0 G s):= by rw [ B_shape G s ]; exact lap_cr G _
    have ht: Garment.veil (B0 G s) := by rw [B_shape]; exact voile_W G _
    exact ( ascent hx ).add (loopC (he 0) rB (ht 0) ⟨_,rfl⟩ hx hv)
lemma sAA (hx:Solid false v q)(he:Solid false w r): Solid false (( Φ G s ).X v w) (q+r):= by obtain ht:=treeC (kred G s 0) (cl_a G s 0) (reverse_a G s 0) (voile_a G s 0) (show ∃ _,A0 G s 0= Landau.choir _ id from ⟨Landau.line _,rfl⟩) hx he; rw [add_zero] at ht; exact ht
lemma sAB (hx:Solid false v q)(he:Solid false w r): Solid false ((Φ G s).C v w) (q+r+1):= by
    have hh: Credit 1 (B0 G s):= by rw [ B_shape G s ]; exact lap_cr G _
    have ht: Garment.veil (B0 G s):= by rw [ B_shape ]; exact voile_W G _
    exact treeC (hh 0) (cl_b G s 0) (reverse_b G s 0) (ht 0) ⟨_,rfl⟩ hx he
end YM.FVA2.O.Ward
