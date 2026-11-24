import YM.SchemeConversionRG11.FirstW.Ore.Mont
/-! High weight continuity for polynomial subtraction residual. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function MeasureTheory Filter Set Metric Topology Lattice Pert Align Laurent Position Deck SchemeConversionRG11
open scoped BigOperators Classical ContDiff
variable {G:Gauge}{T:Itinerary}{F:Labels.Frames G}{c:ℕ→Side}{Q : Wash}{B:ℕ→Pack F}
def bleach (T:Itinerary)(Q:Wash)(B:Pack F)(i:ℕ)(p:E F 6): Weather G := dew T i Q p - ballot (taxes 6 0 1) (cloak F (B.val p))
lemma smear (T:Itinerary)(Q:Wash)(B:Pack F)(i:ℕ)(p:E F 6)(x y:Field4 G) : bleach T Q B i p x y=dew T i Q p x y- chord x y (Full.sections 6 F (B.val p)) := by
 unfold bleach; have hh : uncap (cloak F (B.val p))∈ Reel G := by rw [stretch]; exact (suitsP B).sees p
 rw [LinearMap.sub_apply,LinearMap.sub_apply, ←ballots _ hh x y,stretch]
lemma bleach_sym (T:Itinerary)(Q:Wash)(B:Pack F)(i:ℕ)(p:E F 6)(x y:Field4 G): bleach T Q B i p x y=bleach T Q B i p y x:=by rw [smear,smear,chord_com, dew_val,dew_val, add_comm (saleF T i Q p y x)]
-- supplement high-weight control. all d4 polinears, scaled by one.
lemma high_t (hc:MarkGrid T c)(q:Wash)(a b:Who G 6)(ha:fee a=2)(hb:fee b=2)(A:la G) : Helen (fun i=> T.gap i * sectorA (tin G (T.period i)) 1 0 (wheelS G T i q) a b A.val) := by
 have he:=oneM_credits a b ha hb (fun _=> A.val) (pol_live T (q.rOut+1) A.val A.property) (lt_add_one q.rOut)
 have hQ:=knownP (T:=T) 4 A.val A.property
 obtain ⟨p,hp⟩:= playRoof _ hc q a b ha hb he (by decide) (by norm_num; exact hQ _) -- inspect
 have e : ∀ x:Edge Cover,Honey (fun _:ℕ=> A.val x) := fun _=>Honey.helen ⟨_,tendsto_const_nhds⟩
 have hB:=(stayB _ _ a.val (Honey.tint T b) e).sink T.cutoff
 refine ⟨_,((hp.const_mul 3).add (hB.const_mul 2)).congr fun i=>?_⟩; change 3*(T.gap i^(_ :ℤ)*_)+2*(T.gap i* _) = _
 rw [sector_eq,echoLeg,one_pow,inv_one,one_smul]; norm_num; unfold pit; ring
lemma tintW (hc:MarkGrid T c)(Q:Wash)(p:E F 6)(X Y:la G): Helen (fun i=>T.gap i • saleF T i Q p X.val Y.val) := by
 simp only [saleF,burn_eq,Finset.smul_sum]; apply collectH; intro i _; apply collectH; intro j _; apply collectH; intro k _
 by_cases ht:root3 (cloak F p) i j k=0; · simp only [ht,zero_mul,smul_zero]; exact ⟨0,tendsto_const_nhds⟩
 obtain ⟨_,hk,H⟩:=top_six F p i j k ht; obtain ⟨v,hv⟩:= high_t hc Q i j H hk X; have hm:=hv.mul_const (native k.val 0 Y.val); have hY:= (Complex.continuous_ofReal.continuousAt.tendsto.comp hm).const_mul (root3 (cloak F p) i j k)
 refine ⟨_,hY.congr fun t=>?_⟩; dsimp only [comp_apply]; rw [Complex.real_smul]; push_cast; unfold native; ring
lemma soot (B:Pack F)(p:E F 6)(A C:la G)(q:CheckQ F)(h:q.a=A)(k:q.b=C)(z:q.p=p): rate q (glyph F B)=chord A.val C.val (Full.sections 6 F (B.val p)):=by change (glyph _ _).val _ _ _ = _; rw [h,k,z,tune_eq]
lemma tintZ (Q:Wash)(hc:MarkGrid T c)(p:E F 6)(B:ℕ→Pack F)(h:Level (fun i=> T.gap i • B i))(A C:la G): Helen (fun i=> T.gap i • bleach T Q (B i) i p A.val C.val) := by
 obtain ⟨q,hq⟩:=tintW hc Q p A C; obtain ⟨t,ht⟩:= tintW hc Q p C A; let k:CheckQ F:=⟨p,4,4,A,C,A.property,C.property⟩
 have hp:= Level.map (U:=Pack F) (V:=Bond F) (glyph F) h -- avoid i+j cap, lowCost anyway
 have hp:= lowCost (rate k) hp; simp only [map_smul] at hp; have hX:= ((((hq.add ht).const_mul (2:ℂ)⁻¹).sub hp))
 refine ⟨_,hX.congr fun i=>?_⟩; rw [soot _ p A C k rfl rfl rfl,smear,dew_val]; simp only [Complex.real_smul]; ring
lemma scaled_ball (hc:MarkGrid T c)(Q:Wash)(H:paidC T 5 (fun i=> bondM F T i Q - glyph F (B i)))(h:Level (fun i=>T.gap i • B i))(p:E F 6)(x y:la G)(a b:ℕ)(hx:x.val∈cabin G a)(hy:y.val∈cabin G b) : Helen (fun i=> T.gap i ^ ((a:ℤ)+b-4) • bleach T Q (B i) i p x.val y.val) := by
 by_cases ht:a+b≤4
 · let q:CheckQ F:=⟨p,a,b,x,y,hx,hy⟩; have he(i:ℕ) : rate q (bondM F T i Q - glyph F (B i))= bleach T Q (B i) i p x.val y.val:=by rw [map_sub,soot _ p x y q rfl rfl rfl,smear, show rate q (bondM F T i Q)=dew T i Q p x.val y.val from bond_paid ..]
   obtain ⟨t,h⟩:= H (a+b) (by omega) q rfl; refine ⟨_,h.congr fun i=>?_⟩; dsimp only; rw [he,show (↑a:ℤ)+b-4= -((4-(a+b):ℕ):ℤ) by rw [Nat.cast_sub ht]; omega, zpow_neg,zpow_natCast]
 refine closeHold (a:=1) (T:=T) (f:=fun i=> bleach T Q (B i) i p x.val y.val) (by omega) ?_; simp only [zpow_one]; exact tintZ Q hc p _ h x y
end YM.RG11.FirstW
