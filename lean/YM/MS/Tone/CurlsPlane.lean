import YM.MS.Tone.Curl

/-!
# Wilson transverse S₂ symbol at each momentum plane


 Rank2 gauge only energy. Leg offsets consistent. Upper rank costs elsewhere
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Tone.Frame
open Function Filter Set Finset Plane Koszul Cylinder Lab Taylor Lattice Native Bare Focus Landau Momentum Orient Draft Sew Native.Chart
open Complex (I)
open scoped Topology ContDiff
variable {G:Gauge}(p:QP) (i j:Axis)

def coreCurl (x:PlaqAxes) : ℝ:= blade x.val.1 x.val.2 i p*blade x.val.1 x.val.2 j p
lemma two_faces (f: Axis × Axis→ℝ)(h:∀ i:Axis,f (i,i)=0)(hp:∀ i j,f (i,j)=f (j,i)):
    2*∑ x:PlaqAxes, f x.val =∑ i:Axis,∑ j:Axis,f (i,j):= by
    let u (i j:Axis):=if i< j then f (i,j) else 0
    have hw i j : f (i,j)=u i j + u j i:= by
       unfold u; rcases lt_trichotomy i j with H|H|H; simp [H,H.asymm]; subst i; simp [h]; simp [H,H.asymm]; rw [hp]
    have he : ∑ x:PlaqAxes,f x.val=∑ i:Axis,∑ j:Axis,u i j:= by
       calc
         _ = ∑ x∈ (Finset.univ.filter (fun x: Axis×Axis=>x.1 < x.2)), f x:= by
                 refine Finset.sum_bij (fun x _=> x.val) (fun x _=>Finset.mem_filter.mpr ⟨Finset.mem_univ _,x.property⟩) ?_ ?_ (fun _ _=> rfl) -- no yd
                 · exact fun _ _ _ _ hh=> Subtype.ext hh
                 intro x hx; exact ⟨⟨x,(Finset.mem_filter.mp hx).2⟩,Finset.mem_univ _,rfl⟩
         _ = _ := by rw [Finset.sum_filter, Fintype.sum_prod_type]
    conv_rhs => arg 2; intro i; arg 2; intro j; rw [hw]; -- recursive simp
    rw [he]; simp_rw [Finset.sum_add_distrib]; nth_rw 3 [Finset.sum_comm]; ring
lemma normalcurl : ∑ x:PlaqAxes, coreCurl p i j x= precision i j (wave p):=by
    let f (k:Axis×Axis):= blade k.1 k.2 i p*blade k.1 k.2 j p
    obtain he := two_faces f (fun i=> by simp [f,blade]) (fun i j=> by unfold f blade; ring)
    apply mul_left_cancel₀ (show (2:ℝ)≠0 by norm_num)
    change 2*(∑ x:PlaqAxes,f x.val)=_
    rw [he]; unfold f blade precision delta Momentum.sq -- sq ambiguous
    -- sums distribute & simplify
    simp_rw [sub_mul,mul_sub, sum_sub_distrib]; simp only [ite_mul,mul_ite,zero_mul,mul_zero]; -- both nested condition still
    by_cases H:i=j <;> simp [H,pow_two] <;> ring
lemma wave_neg (p:QP): wave (-p) = -(wave p):= by ext; simp [wave,theta]
lemma sawcurl (x:PlaqAxes)(c k:Conn G): ∑ a:Conn G,curl x (waveForm p i c) a* curl x (waveForm (-p) j k) a=matchA c k (coreCurl p i j x:ℂ):= by
   simp_rw [curl_piece]; unfold matchA; simp only [ite_mul,zero_mul, mul_ite,mul_zero]; rw [Fintype.sum_ite_eq]; by_cases h:c=k; swap; · simp [h]
   have hv : blade x.val.1 x.val.2 j (-p)= -(blade x.val.1 x.val.2 j p):= by unfold blade; rw [wave_neg]; split_ifs <;> simp [sub_eq_add_neg,add_comm]
   rw [h]; simp only [if_true,hv,saw,opp,coreCurl];
   field_simp [(nonz p (z x.val.1+z x.val.2))]; ring_nf; simp [mul_comm]
lemma normW (c k:Conn G): run (weightW G idRail (0:Cover)) [waveForm p i c,waveForm (-p) j k]= matchA c k (-(precision i j (wave p):ℂ)):= by
   have he (x:PlaqAxes) : run (Sew.art (loadC idRail (0,x)) gone) [waveForm p i c,waveForm (-p) j k]= - matchA c k (coreCurl p i j x:ℂ):= by change run (Sew.art (front x) gone) _=_; rw [charge2,sawcurl]
   simp_rw [weightW,map_sum,Finset.sum_apply,he]
   by_cases H : c=k; · unfold matchA; simp_rw [if_pos H,Finset.sum_neg_distrib,← Complex.ofReal_sum,normalcurl]
   simp [matchA,H]
lemma curl_off (p:QP)(x:PlaqAxes)(c: Conn G)(w:Branch G Axis)(h:∀ i:Axis,w.1≠ Landau.gauge i): curl x (w,p) c=0:= by unfold curl; apply Finset.sum_eq_zero; intro i _; rw [show paywave _ _=0 from Classical.byContradiction (fun he=> h (front x i.1).2 (congr_arg Prod.fst (in_light (w,p) (knot (front x) i) he))),zero_mul]
lemma w_off (p q: LightMode G QP)(h:(∀ i:Axis,p.1.1≠Landau.gauge i) ∨ (∀ i:Axis,q.1.1≠Landau.gauge i)): run (weightW G idRail (0:Cover)) [p,q]=0:= by
   simp only [weightW,map_sum,Finset.sum_apply]; apply Finset.sum_eq_zero; intro i _; rw [show run (Sew.art (loadC idRail (0,i)) gone) [p,q]= _ from charge2 i p q]; rcases p with ⟨s,p⟩; rcases q with ⟨t,q⟩; rcases h with H|H <;> first| solve| simp [curl_off p i _ s H]| simp [curl_off q i _ t H]
end YM.MS.Tone.Frame
