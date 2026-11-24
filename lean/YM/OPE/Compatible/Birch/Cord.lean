import YM.OPE.Compatible.Birch.Note
/-! # Wired cotton reading. Axis grouping. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free WithLp Work.F08 Matrix Bloch Precision Planned.PrimaryIntegral295.Carrier
open scoped Topology BigOperators Classical
variable {I J W:Type*}{i j n r d m:ℕ}{G:Gauge}{s b U D:ℝ}{N:Side}
namespace Script
open Page
-- exact one anchored link sum. diff coordinate rho plus root marker. avoid reorder periodic scribe noise. Wick real
variable [Fintype I]{A:Row I I}{p:Script I (r+1)}{q:Script I (d+1)}{x:Fin r→deck I N}{y:Fin d→deck I N}
abbrev Tab (I:Type*) (N:Side):= Site N × I
abbrev deltaH {I:Type*}(x: Tab I N): deck I N:=Pi.single x 1
def drawP (D:Matrix (Tab I N) (Tab I N) ℝ)(p:Script I (r+1))(q:Script I (d+1))(x: Fin r→ deck I N)(y: Fin d→ deck I N)(s t:Site N):= ∑ i:Tab I N, ∑ j:Tab I N,D i j * scribe s p (Fin.cons (deltaH i) x)*scribe t q (Fin.cons (deltaH j) y)
omit [Fintype I] in
lemma Tsumm (h: Summable p): soot 0 p (∑' i,‖p i‖):=by unfold soot Sack Page.figure poise; simp only [pow_zero,one_mul]; exact ⟨fun i=>norm_nonneg _,h.norm,le_rfl⟩
omit [Fintype I] in
lemma cotton_s (h:Whole A)(hp:Summable p)(hg:Summable q):Summable (ticketX A p q):=by
    obtain ⟨s,T,h,hh⟩:=h; apply (cottonPile (strip_mono hh le_rfl (le_max_left T 0)) h (le_max_right T 0) (Tsumm hp) (Tsumm hg)).water; intro i; exact (show 1 ≤ coal 0 i by unfold coal figure poise; simp)
private def firstSlot {n} (p:Page I (n+1)) (x: Site N): Tab I N:=(x+wrap N (p 0).1,(p 0).2)
omit [Fintype I] in
lemma renderer (p:Page I (r+1))(x:Fin r→deck I N)(z:Tab I N)(b:Site N):render b p (Fin.cons (deltaH z) x)= if z=firstSlot p b then render b (mort p) x else 0:=by unfold render; rw [Fin.prod_univ_succ]; change deltaH z (firstSlot ..)*_= _; unfold deltaH; split_ifs with hv; rw [hv, Pi.single_eq_same,one_mul];rfl; rw [Pi.single_eq_of_ne (Ne.symm hv),zero_mul]
lemma wings (A:Matrix (Tab I N) (Tab I N) ℝ)(hp:Summable p)(hh:Summable q)(x: Fin r→deck I N)(y:Fin d→deck I N)(s t: Site N):
   HasSum (fun i:Page I (r+1)× Page I (d+1)=> p i.1 * q i.2*A (firstSlot i.1 s) (firstSlot i.2 t)*render s (mort i.1) x*render t (mort i.2) y) (drawP A p q x y s t):=by
    let f(i j:Tab I N)(p':Page I (r+1) × Page I (d+1)):=A i j * (p p'.1 * render s p'.1 (Fin.cons (deltaH i) x))*(q p'.2*render t p'.2 (Fin.cons (deltaH j) y))
    have he(i j:Tab I N): HasSum (f i j) (A i j * scribe s p (Fin.cons (deltaH i) x)*scribe t q (Fin.cons (deltaH j) y)):=by
       have ha := ((instruments p hp s (Fin.cons (deltaH i) x)).summable).mul_left (A i j); have hb := (instruments q hh t (Fin.cons (deltaH j) y)).summable; have ht:Summable (f i j) := (ha.norm.mul_norm hb.norm).of_norm
       unfold scribe; rw [← tsum_mul_left (a:=A i j),ha.tsum_mul_tsum hb ht]; exact ht.hasSum
    convert! hasSum_sum (s:=univ) (fun i (_:i∈univ)=> hasSum_sum (s:=univ) (fun j (_:j∈univ)=> he i j)) using 1 -- args
    ext1 v; unfold f; simp_rw [renderer]; simp only [mul_ite,ite_mul,zero_mul,mul_zero,sum_ite_eq', Finset.mem_univ,if_true]; ring
omit [Fintype I] in
private lemma transitS (h: Whole A) (s:Site N) (i j:I)(k:Cover)(f:Site N→ℝ): (∑ t:Site N,(A.acts N) (s,i) (t+wrap N k,j)*f t)=∑' u:Cover,A i j u*f (s+wrap N u-wrap N k):=by
     let Y:= Equiv.subRight (wrap N k)
     calc
       _= ∑ t:Site N,(A.acts N) (s,i) (Y t+wrap N k,j)* f (Y t):= (Y.sum_comp (fun t=> _ * f t)).symm
       _= ∑ t:Site N,(A.acts N) (s,i) (t,j) * f (Y t):= Finset.sum_congr rfl fun t _=>by rw [show Y t+wrap N k=t from sub_add_cancel ..]
       _= _:= by
          change (∑ t:Site N,sift (A i j) N s t * f (t-wrap N k))=_
          exact sift_action ((h.safe i j).of_norm) N s (fun t=> f (t-wrap _ k))
lemma readCotton (h: Whole A)(hp:Summable p)(hh:Summable q)(x: Fin r→deck I N)(y:Fin d→deck I N)(b:Site N): scribe b (cotton A p q) (Fin.append x y)= ∑ i:Site N,drawP (A.acts N) p q x y b i:=by
     let v:= Fin.append x y; let u(i:Embers I r d):= ticketX A p q i * render b (rendX i) v
     have hu: Summable u:= ((cotton_s h hp hh).norm.mul_right (∏ i, ‖v i‖)).of_norm_bounded (fun i=> by
       unfold u; rw [norm_mul]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); unfold render; rw [norm_prod]; apply prod_le_prod (fun _ _=> norm_nonneg _);exact fun i _=> norm_le_pi_norm _ _)
     unfold scribe cotton; rw [Sack.cart_bill rendX (fun i=> render b i (Fin.append x y)) hu, hu.tsum_prod]; -- RHS interchange via wings
     let Y(t: Site N)(i:Page I (r+1) × Page I (d+1)):=p i.1 * q i.2*(A.acts N) (firstSlot i.1 b) (firstSlot i.2 t)*render b (mort i.1) x *render t (mort i.2) y
     have ht(t): HasSum (Y t) _:= wings (A.acts N) hp hh x y b t; erw [← (hasSum_sum (s:=univ) (fun j _=>ht j)).tsum_eq]
     refine tsum_congr fun i=>?_ ; let e:=firstSlot i.1 b; let k:Cover:= (i.2 0).1; let W(t:Site N):= (t+wrap N k,(i.2 0).2); let f(t:Site N):=render t (mort i.2) y; have H: (∑ t:Site N,(A.acts N) e (W t)* f t)=∑' j:Cover,A e.2 (i.2 0).2 j *f (e.1+wrap N j-wrap N k):= transitS h e.1 e.2 (i.2 0).2 k f

     have hh(j:Cover): u (i,j)=p i.1*q i.2*render b (mort i.1) x*(A e.2 (i.2 0).2 j*f (e.1+wrap N j-wrap N k)):=by
        change ((p i.1*q i.2*A e.2 _ j)*render b (Fin.append _ _) v)=_; let U:= slide (tideAt i.1 i.2 j) (mort i.2)
        rw [show render b (Fin.append (mort i.1) U) v= render b (mort i.1) x*f _ from ?_]; ring
        unfold render v f; rw [Fin.prod_univ_add]; simp only [Fin.append_left,Fin.append_right]; apply congr_arg; unfold U Page.slide; dsimp only [Equiv.coe_fn_mk]; apply Finset.prod_congr rfl; intro t _; apply congr_arg; ext1; swap; · rfl
        unfold tideAt; simp only [_root_.map_sub,_root_.map_add]; change b+(wrap N (i.1 0).1+ wrap N j-wrap N k+_)=(b+wrap N (i.1 0).1 +_-_)+_; abel
     change ∑' j:Cover, u (i,j)=∑ t:Site N,Y t i; simp_rw [hh]; rw [tsum_mul_left,← H, Finset.mul_sum]; unfold Y; apply Finset.sum_congr rfl; intro a _; change _*(A.acts N e (W a)*f a)=_* A.acts N e (W a)*_*f a; ring
end Script
end YM.OPE.Flume
