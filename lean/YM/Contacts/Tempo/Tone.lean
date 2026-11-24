import YM.Contacts.Tempo.Road
namespace YM.Contacts.Tempo
open Set Filter Finset
open scoped Topology Classical BigOperators NNReal
noncomputable section
variable {n i j d k:ℕ}{κ:Type}{m:κ→ℕ}{v g w f:κ→ℕ→ℝ}{P:κ→ℕ→ℝ→Prop}{b c u:ℝ}
def Runs (c:ℝ)(f v :κ→ℕ→ℝ):Prop:= ∀ p i, v p (i+1)=c*v p i+f p i
lemma Runs.add (h:Runs c f v)(hx:Runs c g w): Runs c (fun x i=>f x i+g x i) (fun x i=>v x i+w x i):= fun x i=> by dsimp; rw [h,hx]; ring
lemma Runs.sub (h:Runs c f v)(hx:Runs c g w): Runs c (fun x i=>f x i-g x i) (fun x i=>v x i-w x i):= fun x i=> by dsimp; rw [h,hx]; ring
-- unstable moment along logarithmic scales
variable (m d v b)
def Pads : Prop:= ∀ p i,‖v p i‖≤ b*toll (m p) i d
variable {m d v b}
lemma wash (hp: Pads d m f b)(hb:0≤b)(hv:0 < u) (n k:ℕ)(p:κ): ‖f p (n+k)*u^k‖≤ (b*toll (m p) n d)*(toll 0 k d*u^k):= by rw [norm_mul,norm_pow,Real.norm_of_nonneg hv.le]; apply le_trans (mul_le_mul_of_nonneg_right ((hp p _).trans (mul_le_mul_of_nonneg_left (toll_tri _ _ n _) hb)) (pow_nonneg hv.le k)); rw [toll_add k n]; exact le_of_eq (by ring)
lemma wash_sum (hp: Pads d m f b)(hb:0≤b)(hv:0<u)(hu:u<1)(p:κ)(n:ℕ) :Summable (fun k:ℕ=> ‖f p (n+k)*u^k‖):= ((series_toll d hv hu).mul_left (b*toll (m p) n d)).of_nonneg_of_le (fun _=> norm_nonneg _) (fun k=> wash hp hb hv n k p)
def gain (v:ℝ)(f :κ→ℕ→ℝ):κ→ℕ→ℝ:= fun p n=> (∑' k:ℕ,f p (n+k)*v⁻¹^k) * -v⁻¹
namespace Rates
variable (h:Rates m f)
include h
lemma prices (hc:1<c): Rates m (gain c f) ∧ Runs c f (gain c f):= by
   let u:=c⁻¹; have hu: 0<c:= lt_trans zero_lt_one hc; have hx:0<u:= inv_pos.mpr hu; have hu':u<1:= inv_lt_one_of_one_lt₀ hc; obtain ⟨d,b,hb,H⟩:= h; let P:=fun x:ℕ=>toll 0 x d*u^x; let w:= tsum P; have hW: Summable P:= series_toll d hx hu'; have hw: 0≤w:= tsum_nonneg (fun _=>mul_nonneg (toll_glow ..).le (pow_nonneg hx.le _)); let f'(p:κ)(i k:ℕ):= f p (i+k)*u^k; have hs(p i):=wash_sum (m:=m) (d:=d) (f:=f) H hb hx hu' p i
   constructor; · refine ⟨d,b*w*u,mul_nonneg (mul_nonneg hb hw) hx.le,fun x i=> ?_⟩; change ‖tsum (f' x i)* -u‖≤_; rw [norm_mul,norm_neg,Real.norm_of_nonneg hx.le]; refine (mul_le_mul_of_nonneg_right (c:=(b*toll (m x) i d)*w) ((norm_tsum_le_tsum_norm (hs x i)).trans ?_) hx.le).trans_eq (by ring); rw [show b*toll (m x) i d*w=∑' n,(b*toll (m x) i d)*P n from tsum_mul_left .. |>.symm ]; exact Summable.tsum_le_tsum (fun k=> wash H hb hx i k x) (hs x i) (hW.mul_left _)
   intro p i; let X:= tsum (f' p (i+1)); let T:=tsum (f' p i); change X* -u=c*(T * -u)+_; rw [show T=f p i+X*u from ?_]; · unfold u; field_simp; ring
   let hx:= (hs p i).of_norm; rw [show T=_ from hx.tsum_eq_zero_add]; change f' p i 0+_= _; unfold X; rw [← tsum_mul_right]; simp only [f',Nat.add_zero,pow_zero,mul_one]; congr 1; apply tsum_congr; intro x; rw [pow_succ]; have he:i+(x+1)=i+1+x:= by omega
   rw [he,mul_assoc]
-- uniqueness: individual profiles at nonuniform polynomial rates suffice (used upon marking measuring point)
omit h
lemma sole (h:Rates m v)(he:Rates m w)(hc:1<c)(H:Runs c f v)(Q:Runs c f w): v=w:= by
   let x (p :κ)(i:ℕ):=v p i-w p i; have hX: Rates m x:= h.sub he; obtain ⟨d,b,hb,Y⟩:= hX; have hq:0<c:= lt_trans zero_lt_one hc; have hr p (i:ℕ): x p (i+1)=c*x p i:= by unfold x; rw [H,Q,mul_sub]; ring
   funext p i; let u:= c⁻¹; have hU:0<u:= inv_pos.mpr hq; let A:=wash_sum (f:=x) Y hb hU (inv_lt_one_of_one_lt₀ hc) p i; have h' (j:ℕ): x p (i+j)*u^j=x p i:= by
      induction j with|zero=>simp only [Nat.add_zero,pow_zero,mul_one]|succ j ih=>rw [← Nat.add_assoc,hr,pow_succ]; rw [show c*x p (i+j)*(u^j*u)=x p (i+j)*u^j from by unfold u; field_simp]; exact ih
   have he: Tendsto (fun (_:ℕ)=> ‖x p i‖) atTop (𝓝 0):= by simpa only [h'] using A.tendsto_atTop_zero
   exact sub_eq_zero.mp (norm_eq_zero.mp (tendsto_nhds_unique tendsto_const_nhds he : ‖x p i‖=0))
lemma solo_dist (z:κ)(hv:Rates (fun _:Unit=>m z) (fun (_:Unit) i=> v z i))(hw:Rates m w)(hc:1<c)(H:Runs c f v)(Q:Runs c f w): v z i=w z i:= by obtain ⟨d,b,hb,U⟩:= hw; exact congr_fun (congr_fun (sole hv (f:=fun (_:Unit) i=> f z i) (w:=fun _ i=> w z i) ⟨d,b,hb,fun _ i=>U z i⟩ hc (fun _ i=> H z i) (fun _ i=> Q z i)) ()) i
lemma assured (h:Rates m f) (hx:∀ p,Rates (fun _:Unit=>m p) (fun (_:Unit) i=> v p i))(hc:1<c)(H:Runs c f v): Rates m v:= (show gain c f=v from (funext fun x=> funext fun i=> (solo_dist x (hx x) (prices h hc).1 hc H (prices h hc).2).symm)) ▸ (prices h hc).1
end Rates
end
end YM.Contacts.Tempo
