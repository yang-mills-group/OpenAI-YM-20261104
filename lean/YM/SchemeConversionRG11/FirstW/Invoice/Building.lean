import YM.SchemeConversionRG11.FirstW.Invoice.Attic
/-! Gauge linear read vs correlated tags. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW.Deck
open Function Filter MeasureTheory ProbabilityTheory Set Lattice Pert Warp Topology Align
open scoped BigOperators Classical
variable {n : Side} {G : Gauge} {d r : ℕ} {h : ℝ}
def pick (r d : ℕ) (u : Ear G (Per n)) : Query (Ribs G n r d) := Complex.ofRealCLM.comp (Warp.chain (Full.Aux G d) r (strike (picks (reduced u))))
def spanT (x : Orb.Coords G n) := ((Orb.expand G n x).val : FullT G n)
lemma pick_roll (u : Ear G (Per n)) (x : Ribs G n r d) : pick r d u x=(u (spanT x.fst):ℝ) := by change (↑(strike (picks (reduced u)) x.1):ℂ)=_; rw [strike_eq,dot_expand];rfl
lemma pick_laugh (u : Ear G (Per n)) : Laugh (hall G n r d h) (pick r d u) := by
  letI := Orb.isLaw (G:=G) (n:=n)
  letI := Full.auxGaussian (G:=G) (d:=d) h
  let L : Orb.Coords G n→ℂ := fun x=> ↑(strike (picks (reduced u)) x)
  have hv : (∫ x,L x ∂Orb.data G n)=0 := by unfold L; rw [integral_complex_ofReal,field_mean]; rfl
  have he := mix_pair (Orb.data G n) (Full.auxLaw G d h) r L (fun _ _=> 1)
  simp only [Finset.prod_const_one,mul_one,hv,zero_mul] at he; exact he
lemma pick_form (u t : Ear G (Per n)) : coins (hall G n r d h) (pick r d u) (pick r d t) = (t (tbranch G n u+reflectT G n (tbranch G n u)):ℝ) := by
  letI := Orb.isLaw (G:=G) (n:=n)
  letI := Full.auxGaussian (G:=G) (d:=d) h
  let X(x : Orb.Coords G n):ℂ := ↑(strike (picks (reduced u)) x)*↑(strike (picks (reduced t)) x)
  have hv : (∫ x,X x ∂Orb.data G n) = (↑(Align.jointB G n (reduced u) (reduced t)):ℂ) := by unfold X;simp_rw [← Complex.ofReal_mul, integral_complex_ofReal, field_quad,dot_inverse]
  have he := mix_pair (Orb.data G n) (Full.auxLaw G d h) r X (fun _ _=> 1); simp only [Finset.prod_const_one,mul_one,hv,integral_const,probReal_univ,one_smul,pinch_potential] at he; simpa only [Finset.prod_const_one,mul_one] using! he
variable (h) (o : Full.Grid n r)
def arise (v : At G r d) := river h v.2.val (o v.1)
def cloudK (v : At G r d) := arise h o v+reflectT G n (arise h o v)
lemma pick_here (u : Ear G (Per n)) (v : At G r d) : coins (hall G n r d h) (pick r d u) (teams o h v) = (u (cloudK h o v):ℝ) := by
  letI := Orb.isLaw (G:=G) (n:=n)
  letI := Full.auxGaussian (G:=G) (d:=d) h
  let f := Orb.data G n; let a:=Full.auxLaw G d h
  let p:=firsthand h (o v.1) v.2.val
  let q:=strike (picks (reduced u))
  have e (x:Ribs G n r d) : floating (Orb.Coords G n) (Full.Aux G d) v.fst q 0 x= pick r d u x := by rw [floating_eq,flight]; simp only [zero_apply,Complex.ofReal_zero, mul_zero,add_zero]; rfl
  have hv := Warp.float_prod f a v.1 v.1 (g1:=Warp.guest v.2) (g2:=0) (f1:=p) (f2:=q) (guest_mean h ..) (by simp)
  simp_rw [if_true, zero_apply, mul_zero,integral_zero, Complex.ofReal_zero, sub_zero, e] at hv
  unfold coins; simp_rw [mul_comm ((pick _ _ _) _)]; change (∫ x,node h o v.fst v.snd x * _ ∂hall ..)=_
  apply hv.trans
  unfold p q firsthand; rw [field_quad, show kField h (o v.fst) v.snd.val= picks (reduced (tape v.2.val h (o v.fst))) from by rw [tape_again]; rfl,dot_inverse,pinch_potential]; unfold cloudK arise; rw [gauged]
variable (p : Players G r d)
def row1 (u : Ear G (Per n)) := payOne (hall G n r d h) (teams o h) (feed p) (pick r d u)
def row2 (u v : Ear G (Per n)) := payTwo (hall G n r d h) (teams o h) (feed p) (pick r d u) (pick r d v)
def row3 (u v z : Ear G (Per n)) := payTree (hall G n r d h) (teams o h) (feed p) (pick r d u) (pick r d v) (pick r d z)
def pool (u v : Ear G (Per n)) := v (tbranch G n u+reflectT G n (tbranch G n u))
lemma row2_print (u v : Ear G (Per n)) : row2 h o p u v=pool u v*ZeroR o h p +∑ i:At G r d, ∑ j:At G r d, u (cloudK h o i) * (v (cloudK h o j)*ZeroR o h (dict j (dict i p))) := by
  haveI := hall_G G n r d h
  unfold row2; rw [erase_two]; simp only [pick_form,pick_here,d_feed,← stand,pool]
  · exact fun i=> node_center ..
  exacts [pick_laugh ..,pick_laugh ..]
lemma row3_print (u v z : Ear G (Per n)) : row3 h o p u v z = pool u v * row1 h o p z + pool u z * row1 h o p v + pool v z * row1 h o p u + ∑ i:At G r d, ∑ j:At G r d, ∑ k:At G r d,(u (cloudK h o i)*v (cloudK h o j)*z (cloudK h o k):ℝ)*ZeroR o h (dict k (dict j (dict i p))) := by
  haveI := hall_G G n r d h
  unfold row3; rw [erase_tree]
  · simp_rw [d_feed,pick_here]; simp only [pick_form,row1,pool, Complex.ofReal_mul,←stand]
  · exact fun i=>node_center ..
  exacts [pick_laugh ..,pick_laugh ..,pick_laugh ..]
lemma pre_prices (L : Orb.Coords G n→ℂ) (H : Orb.Tame L) : Integrable (fun x:Ribs G n r d=>L x.fst*spend (teams o h) (feed p) x) (hall G n r d h) := by
  haveI := hall_G G n r d h
  refine price_tame _ (Orb.Tame.mul ?_ (spend_A ..))
  obtain ⟨C,hc,k,Hk⟩:=H.2; refine ⟨H.1.comp continuous_fst,C,hc,k,fun x=>?_⟩; change ‖L _‖ ≤ _; grw [Hk]; gcongr; exact le_max_left ..
end YM.RG11.FirstW.Deck
