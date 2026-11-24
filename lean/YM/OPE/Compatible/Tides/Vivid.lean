import YM.OPE.Compatible.Tides.Polar
/-!
# Critical copy.Relay through any stripes.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Balsam
open Function MeasureTheory Set Topology Metric Filter Lattice Laurent Flume Sagebrush Maxwell Extra.FD SphereTest Analysis
open scoped BigOperators Classical ContDiff
variable {U:Gloam}{d r B:ℝ}{g:ℕ→Cover→ℝ}{k j:ℕ}{R:ℕ→ℕ}{m:Multiset Axis}{f:Cover→ℝ}{F:E4→ℝ}
abbrev Oct (R:ℕ→ℕ)(f:Cover→ℝ)(g:ℕ→Cover→ℝ)(i):= ∑ x∈pod (R i),f x*g i x
abbrev Oar (R:ℕ→ℕ)(m:Multiset Axis)(f:Cover→ℝ)(g:ℕ→Cover→ℝ)(i):= (∑ x∈pod (R i),f x*pine m x)*dvol m.toList (g i) 0
lemma tail_big (hn:Crown U R)(hp:Port U d k g)(hx:0≤B)(hw:∀ x, ‖f x‖≤ B/(notch x:ℝ)^(j+4))(hm:m.card<j): Fruit U (k+j) (Oar R m f g) 0:=by
    let l:=m.card; obtain ⟨u,hu,H⟩: ∃ u:ℕ, 0<u ∧ j=l+u:=⟨j-m.card,by omega,by unfold l; omega⟩
    let G(x):=f x*pine m x; have hg(x):‖G x‖ ≤ B/(notch x:ℝ)^(u+4):=by
       have he:= hw x; have hb:0 < (notch x:ℝ):= Nat.cast_pos.mpr (notch_one x); unfold G; rw [norm_mul]; grw [he, pine_paths]; grw [show (size x:ℝ) ≤ notch x from by unfold notch;push_cast;linarith]; exact le_of_eq (by rw [H,show l+u+4=l+(u+4) from by omega,pow_add]; unfold l;field_simp)
    let A:=∑' x,G x; let L(i:ℕ):=dvol m.toList (g i) 0; let p(i):=∑ x∈pod (R i), G x; have he: Bloom U (k+l) L (slit U (k+l) (stalkP m.toList g)):=by have ha: m.toList.length=l:= Multiset.length_toList _; rw [←ha]; exact (hp m.toList).slit
    have hS:Sake U u (fun i=>p i-A):=by
        obtain ⟨r,hr,h⟩:=hn.small; refine coseal (f:=fun i=>p i-A) ?_ (show 0 ≤16*B/r^u by positivity); filter_upwards [h] with i hi
        rw [norm_sub_rev]; refine (stove hg hu hx (R i)).trans ?_
        calc _ ≤ 16*B/(r/U.h i)^u:=by
                                                                                have he:=U.h_pos i; gcongr; apply (div_le_iff₀ he).mpr; linarith only [hi,he]
             _ = _:=by rw [div_pow]; have he:=U.h_pos i;field_simp
    rw [show Oar R m f g = ((fun _:ℕ=>A)*L)+(fun i=>p i-A)*L from funext fun i=>by change p i*_= _ + (p i-A)*_; change _= A*L i+ _; change p i*L i=_;ring, ← add_zero (0:ℝ)]; apply Fruit.sum (Cleared.sap (Cleared.always.pen he.full)); apply Fruit.call; apply booze_sake; rw [show k+j=u+(k+l) from by omega]; exact hS.pen he.1
lemma tail_even (hn:Crown U R)(hp:Port U d k g)(hq:Quip (↑(j+4:ℕ):ℤ) f F)(hm:m.card=j): Fruit U (k+j) (Oar R m f g) (fineI U.q'⁻¹ (F*horn m)*slit U (k+j) (stalkP m.toList g)):=by
   have hx:= hq.purse (pine_quip m); rw [hm,show (↑(j+4:ℕ):ℤ)+ (-(j:ℤ))=4 from by omega] at hx; let x:= (U.h); change Fruit U _ ((fun i=>∑ p∈pod (R i), (f*pine m) p) * (fun i=> stalkP m.toList g i 0)) _
   have hh:m.toList.length=j:= (Multiset.length_toList _).trans hm; simpa only [zero_add] using! (Fruit.pen (y:=slit U (k+j) (stalkP m.toList g)) (k:=0) (j:=k+j) (g:=fun i=> stalkP m.toList g i 0) (Fruit.call (merry hn hx)) (by rw [← hh];exact (hp m.toList).slit)) -- zero_add
lemma fad (hn:Crown U R)(hp:Port U d k g)(hr:r<d)(hv:∀ᶠ i in atTop,U.h i*R i≤ r)(hq:Quip (↑(j+4:ℕ):ℤ) f F)(ha:∀ x∈away, ContDiffAt ℝ ∞ F x):Fruit U (k+j) (Oct R f g) (fineI U.q'⁻¹ (F*Port.eve U k j g)):=by
   let t:=trail Axis (j+1); let e:= (U.q')⁻¹; have he:0<e:=inv_pos.mpr (zero_lt_one.trans U.qsub)
   let G:=annA e*F; let B(m:Multiset Axis):=slit U (k+j) (stalkP m.toList g); let c(m:Multiset Axis):=fineI e (F*horn m)*B m
   let v(m:Multiset Axis):= if m.card=j then c m else 0
   have hs: fineI U.q'⁻¹ (F*Port.eve U k j g)=∑ m∈t, v m:=by
       let f(m:Multiset Axis):= G*(B m • horn m); have hh(m:Multiset Axis):Integrable (f m):= coal_fin (HasCompactSupport.mul_right (shipA he)) (((horn_pure m).vScale (B m)).smooth.continuous) ((iceAway F ha).continuous)
       change fineI e _=_; unfold v Port.eve fineI; conv_rhs=>rw [←Finset.sum_filter]
       rw [show (fun x=>_)= (fun x:E4=>∑ m∈Port.listX j, f m x) from ?_] -- specify
       rw [integral_finsetSum _ (fun m _=>hh m)]; apply Finset.sum_congr rfl; intro m hm; unfold f c fineI; simp only [G,Pi.smul_apply,Pi.mul_apply,smul_eq_mul]; rw [← MeasureTheory.integral_mul_const]; congr 1; ext x;ring
       funext x
       simp only [Pi.mul_apply,Finset.sum_apply,Finset.mul_sum]; simp only [f,G,Pi.mul_apply,B]; refine Finset.sum_congr rfl (fun i hi=>?_); ring
   obtain ⟨A,hA,h⟩:=Quip_cash hq; simp_rw [zpow_neg,zpow_natCast,← div_eq_mul_inv] at h
   have hl(m:Multiset Axis)(hm:m∈t):Fruit U (k+j) (Oar R m f g) (v m):=by unfold v; split; exact tail_even hn hp hq (by assumption); have hx: m.card<j:= lt_of_le_of_ne ((Nat.le_of_lt_succ ((trailed _ _).1 hm))) (by assumption); exact tail_big hn hp hA h hx
   let L(i):=∑ x∈pod (R i),f x*(g i x-sketch (j+1) (g i) x)
   have hV:L+∑ m∈t,Oar R m f g=Oct R f g:=by
       funext i; rw [Pi.add_apply,Finset.sum_apply]; unfold Oar Oct L; simp_rw [Finset.sum_mul]; rw [Finset.sum_comm, ← Finset.sum_add_distrib]; refine Finset.sum_congr rfl (fun x hx=>?_); simp only [sketch, Finset.sum_apply,smul_eq_mul, mul_sub]; rw [Finset.mul_sum]; simp only [mul_assoc]; unfold t; abel
   rw [←hV,hs, ← zero_add (∑ m∈t,v m)]; exact Fruit.sum (Fruit.call (booze_sake (unfog hn hp hr hv hA h))) (Fruit.line _ _ _ hl)
end YM.OPE.Balsam
