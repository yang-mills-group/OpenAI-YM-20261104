import YM.SchemeConversionRG11.FirstW.Fold.Arrows
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW.Deck
open Function MeasureTheory Filter Set Metric Lattice Pert Align Position Maxwell RawLabels MvPolynomial Warp SchemeConversionRG11
open scoped BigOperators Classical Topology Matrix
variable {G:Gauge}{F:Labels.Frames G}{T:Itinerary}{r:ℕ} {Q:Wash}{R:ℝ}{o:∀ i,Full.Grid (T.period i) r} {v:Points r}{c:ℕ→Side}
def currents (Q:Wash)(T:Itinerary)(o:∀ i,Full.Grid (T.period i) r)(s:Fin r)(i:ℕ): Sky G (Per (T.period i)):= deckP _ (o i s) (wheelS G T i Q)
lemma trust (d:Diorama T o v)(s:Fin r)(a b:Who G 6)(x:At G r 6)(hQ: Q.rOut < R)(hP:8*R < ‖v x.1-v s‖)(hc:MarkGrid T c)(ha:fee a=2)(hb:fee b=2):
 Dear T (fun i=> sectorA (torT _ 6 (T.gap i) (o i s)) (T.gap i) (o i s) (currents Q T o s i) a b (arise (T.gap i) (o i) x)):=by
 let p(i:ℕ):=radX s (o i) (T.gap i) 6 x; let f (i:ℕ):= sectorA (tin G (T.period i)) 1 (0:Cover) (wheelS G T i Q) a b
 obtain ⟨h,B,H,hb'⟩:= (show Coal T Q R p from prints d s x hQ hP)
 let F:= composeR T 4 B; have hp : Messed T (4*R) 4 (p-F):= hb'; have he:=bodym hc a b ha hb R hQ hp (coal_neg h (arms B H))
 obtain ⟨u,hu⟩:= he; have hQ : Tendsto (fun i=> f i (p i)) atTop (𝓝 0):=by
    have hv (i:ℕ): T.gap i ^(4:ℕ)*(T.gap i ^(-4:ℤ))=1:=by rw [zpow_neg,zpow_ofNat, mul_inv_cancel₀ (pow_ne_zero _ (T.positive i).ne')];
    have hh:= ((T.cutoff.pow 4).mul hu).add (zero_poly hc a b ha hb (Q:=Q) H); norm_num only [zero_pow,ne_eq, OfNat.ofNat_ne_zero,not_false_eq_true,zero_mul,zero_add] at hh -- avoid names
    apply hh.congr; intro i; simp only [f,F, ← mul_assoc,hv,one_mul, Pi.sub_apply,map_sub,sub_add_cancel]

 have hp(i:ℕ): sectorA (torT _ 6 (T.gap i) (o i s)) (T.gap i) (o i s) (currents Q T o s i) a b (arise (T.gap i) (o i) x)= (T.gap i^fee a)⁻¹ • ((T.gap i^fee b)⁻¹ • f i (p i)):=by unfold currents; rw [sector_cut,mul_assoc]; simp only [p,f,radX,smul_eq_mul]
 simp_rw [hp]; exact ((Dear.given (T:=T) hQ).sale (fee b)).sale (fee a)
lemma trestle_shift (d:Diorama T o v)(p:Players G r 6)(s:Fin r)(k:E F 6)(Q:Wash)(hQ:Q.rOut<R)(hP:∀ z:Fin r,z≠s → 8*R<‖v z-v s‖)(hc:MarkGrid T c) : Fleck T (fun i=> trestle k (o i) (T.gap i) (currents Q T o s i) (dues (o i) (T.gap i)) s p - trestle k (o i) (T.gap i) (currents Q T o s i) (radar (o i) (T.gap i)) s p) := by
 let L:=ContinuousLinearMap.mul ℝ ℂ
 simp_rw [trestle,← Finset.sum_sub_distrib]; refine Fleck.collect fun i hi=> Fleck.collect fun j hj=>?_ ; simp_rw [←sub_mul]; refine Fleck.with (B:=L) ?_ (zeroth_thin d.hdiv o (dict j (dict i (air p s))) v d.ht d.hs)
 simp_rw [glist,←Finset.sum_sub_distrib]; apply Fleck.collect; intro a _; apply Fleck.collect; intro b _; apply Fleck.collect; intro x _
 by_cases h:root3 (cloak F k) a b x=0; · simp only [h, zero_mul,sub_zero]; exact Fleck.still
 obtain ⟨hw, hb,ha⟩:= top_six F k a b x h; have hz:= trust d s a b i hQ (hP _ (Finset.mem_filter.mp hi).2) hc ha hb
 have hp := (orientedD d (s,x) j (Finset.mem_filter.mp hj).2.symm).push Complex.ofRealCLM
 simp_rw [←mul_sub]; -- mul_sub rew maybe changes core
 simp only [Complex.ofReal_mul,←mul_sub,←Complex.ofReal_sub]; refine Fleck.with (B:=L.flip) ?_ (Dear.given (tendsto_const_nhds));
 exact hp.with (hz.push Complex.ofRealCLM) L.flip
-- local CT: shared cut syntax chosen arbitrarily (orientation, radius). signed across horizons. pointwise ANY coordinates. product residue also exposed for identification (Rim, first test later)
def costCT (F:Labels.Frames G)(Q:Wash)(T:Itinerary)(s:Fin r)(o:∀ i,Full.Grid (T.period i) r)(Z:ℕ→Pack F)(k:E F 6)(p:Players G r 6)(i:ℕ) := group3 p (o i) (T.gap i) s + group2 p (o i) (T.gap i) s (currents Q T o s i) - ZeroR (o i) (T.gap i) (update p s (cloak F ((carryR (T.period i) (T.gap i) (Z i)).val k)))
def billedC (F:Labels.Frames G)(Q:Wash)(T:Itinerary)(o:∀ i,Full.Grid (T.period i) r)(Z:ℕ→Pack F)(k:E F 6)(p:Players G r 6)(s:Fin r)(i:ℕ) := ∑ a∈apart G 6 s,∑ b∈apart G 6 s,(T.gap i ^(-6:ℤ) • bleach T Q (Z i) i k (radX s (o i) (T.gap i) 6 a) (radX s (o i) (T.gap i) 6 b))*ZeroR (o i) (T.gap i) (dict b (dict a (air p s)))
lemma remains (d:Diorama T o v)(p:Players G r 6)(s:Fin r)(k:E F 6)(hx:p s=cloak F k)(Q:Wash)(hQ:Q.rOut<R)(hP:∀ z:Fin r,z≠s → 8*R<‖v z-v s‖)(Z:ℕ→Pack F)(hz:stampB F Z T Q)(hg:G.Simple)(hc:MarkGrid T c):
    Fleck T (fun i=> costCT F Q T s o Z k p i-billedC F Q T o Z k p s i) := by
 have hv (i:ℕ)(u:G.El)(A B C:FullT G (T.period i)): currents Q T o s i (putting u A) (putting u B) (putting u C)=currents Q T o s i A B C := by
    unfold currents deckP; simp only [LinearMap.coe_mk,AddHom.coe_mk,LinearMap.comp_apply,LinearMap.compl₂_apply]; simp only [wash_eq, show ∀ (A:FullT G (T.period i)),terms (o i s) (putting u A)=putting u (terms (o i s) A) from fun A=>rfl,tower_key]
 obtain ⟨hr,hY⟩:= pass_part d Z hz.2 p k s
 have H:= trestle_shift d p s k Q hQ hP hc
 let F₁(i:ℕ):= trestle k (o i) (T.gap i) (currents Q T o s i)
 let q i:= cloak F ((twistC (T.gap i) (Z i)).val k)
 let C i :=echoesP p (o i) (T.gap i) s (q i)
 let U i:= radar (G:=G) (o i) (T.gap i)
 let X (i:ℕ):=echoSelf p (o i) (T.gap i) s (q i)
 have he(i:ℕ) : F₁ i (U i) s p-C i (U i)= billedC F Q T o Z k p s i := by
    unfold F₁ C U q currents; rw [trestle_city,echo_rows s (o i) (T.gap i) p k (T.positive i)]; simp_rw [← Finset.sum_sub_distrib]; unfold billedC; apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _; rw [← sub_mul, smear,smul_sub]
 let f(i:ℕ):=dues (G:=G) (d:=6) (o i) (T.gap i)
 have hx'(i:ℕ): costCT F Q T s o Z k p i-billedC F Q T o Z k p s i=F₁ i (f i) s p-F₁ i (U i) s p + -(X i)+ -(C i (f i)- C i (U i)) := by
    unfold costCT; rw [cap_reads p s _ _ k hx, net_print p s _ _ k hx hg _ (hv i), carryPay]; rw [← he i]; unfold F₁ X C q U f; abel
 simp_rw [hx']; exact (H.roll hr.minus).roll hY.minus
lemma voltC (d:Diorama T o v)(p:Players G r 6)(s:Fin r)(k:E F 6)(Q:Wash)(hQ:Q.rOut<R)(hP:∀ z:Fin r,z≠s → 8*R<‖v z-v s‖)(Z:ℕ→Pack F)(hz:stampB F Z T Q)(hc:MarkGrid T c): Helen (billedC F Q T o Z k p s) := by
 unfold billedC; apply collectH; intro a ha; apply collectH; intro b hb
 obtain ⟨v,H⟩:= burn_paid _ _ hQ (prints d s a hQ (hP _ (Finset.mem_filter.mp ha).2)) (prints d s b hQ (hP _ (Finset.mem_filter.mp hb).2)) k hz hc
 let w:=dict b (dict a (air p s)); exact ⟨_, H.mul (Warp.poly_limit 6 T _ _ d.ht d.hs d.hdiv (fun i=>uncap_height (w i)))⟩
end YM.RG11.FirstW.Deck
