import YM.Contacts.Model.Ham
/-! Pure soft-symbol ⇒ sawtooth bill. No premise on slope derivative
 projections. Spend input Laurent stencil rather than dividing smaller height symbols. -/
noncomputable section
namespace YM.Contacts.Model.Slope
open Function Lattice Finset Filter Set PhysicalNext.Repeat Pressure Wilson MeasureTheory RG
open Slide (Stars)
open Trio (froth Mirrors Offer)
open AnalyticBridge VerifiedReset Push.AbsoluteSums Animals YM.Stationary Milling PertExtension.Series Exterior Precision Ion
open Pulse Spine Garf Steam Bloch Radial House Lumen Metric Laurent
open scoped Topology NNReal InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{m:Side}{n k:ℕ}
-- equivalence between field algebra numbering and torus test
section pole
variable {α:Type}[instZ:Fintype α] {q:Field (Fin 2) (Node α)}{p:Field (Fin 2) (Co m α)}{σ:ℝ≥0}{C:ℝ}(hq: Rooted (terrain σ _) q C) (hr:Shadow (lower m) q p)(ha:∀ i,Mirrored (backpack i) q)
def pairing {V:Type} : V×V≃(Fin 2→V) := ⟨fun x=>![x.1,x.2], fun i=>(i 0,i 1),fun _=>rfl,fun _=>by funext i; fin_cases i<;>rfl⟩
def seconds {V:Type}(a:V) : V ≃ Locked V (0:Fin 2) a := ⟨fun x=>⟨![a,x],rfl⟩,fun x=> x.val 1,fun x=>rfl, fun ⟨x,h⟩=>Subtype.ext (by ext i; subst a; fin_cases i<;> rfl)⟩
def imp (ξ:α)(W:Site m→ℝ)(v:Co m α) := if v.2=ξ then W v.1 else 0
lemma design_long (p:Field (Fin 2) (Co m α))(W:Site m→ℝ)(v:α) : design p (imp v W)=∑ i:Site m,∑ j:Site m,p ![(i,v),(j,v)]* (W i*W j):= by
   letI : DecidableEq (Fin 2):= fun _ _=> Classical.propDecidable _; rw [design_spec]; erw [← Equiv.sum_comp pairing,Fintype.sum_prod_type]; simp_rw [Fintype.sum_prod_type]; refine sum_congr rfl fun i _=> ?_ ; rw [sum_comm]; apply sum_congr rfl; intro j _; unfold imp; -- simplify rhs product
   dsimp only [pairing]; simp_rw [Fin.prod_univ_two]; simp [ite_mul,mul_ite] -- warning
include hq hr ha
variable (v:α)(W:Site m→ℝ)
local notation "b" => (extract q ![v,v] : Shift (Keys 1)→ℝ)
omit instZ hq in
lemma cellpack (i j:Site m) : p ![(i,v),(j,v)] = ∑' t:Tailor 1, if j=i+wrap m (legLane t 1) then b t else 0:= by
   let L:= lower (α:=α) m; let a:= lift i; let y:= (a,v); let z:= (i,v); let Q:= Locked _ (0:Fin 2) y; let K:= ![(i,v),(j,v)]; rw [← wrap_lift i] -- maybe bad
   let h:wrap m a=i:= wrap_lift i; rw [h]
   let T:= ((seconds (L y)) ⟨j,v⟩); have ht:=hr (0:Fin 2) y T; rw [show p ![_ , _]=_ from congr_arg _ (show K=T.val from congr_arg₂ (fun a k:Co m α=>![a,k]) (Prod.ext h.symm rfl) rfl)]; dsimp only at ht; rw [ht]; rw [MergeProof.expand_eq]
   let Y t :Q:= ⟨publish a ![v,v] t,by simp [y,publish,legLane]⟩; have hY:Injective Y:= fun i j h=> by simpa only [Y,deg_issue] using congr_arg (fun p:Q=> Spine.degree p.val) h
   rw [← hY.tsum_eq]; swap; 
   · intro x hx; have he:= hx; change (if roll L _ _ x=T then _ else (0:ℝ))≠0 at hx; split at hx;
     next hh=>
      have hk : alphabet x.val=![v,v]:= by funext j; fin_cases j; exact congr_arg Prod.snd x.property; exact congr_arg Prod.snd (congr_fun (congr_arg Subtype.val hh) 1)
      exact ⟨Spine.degree x.val,Subtype.ext (Eq.trans (by rw [hk] ; congr; exact (congr_arg Prod.fst x.property).symm : publish a ![v,v] (Spine.degree x.val)=publish (x.val 0).1 (alphabet x.val) (Spine.degree x.val)) (retrieve x.val))⟩ -- rw orientation
     exact False.elim (hx rfl)
   apply tsum_congr; intro t; have hz : roll L (0:Fin 2) y (Y t)=T ↔ j=i+wrap m (legLane t 1):= by
      have hW : ((roll L _ y (Y t)).val 1)= (i+wrap m (legLane t 1),v):=Prod.ext ((map_add ..).trans (congr_arg (· + wrap m (legLane t 1)) h)) rfl
      rw [← (seconds (L y)).symm.injective.eq_iff]; change (roll L _ y _).val 1=(j,v)↔_; rw [hW]; simp [eq_comm]
   rw [if_congr hz ?_ rfl]; rw [show (Y t).val= _ from (show (Y t).val= backpack a ∘ publish 0 ![v,v] t from funext (fun i=>Prod.ext (by change a+ _=0+(legLane t i)+a; abel) rfl)),ha]; rfl
omit instZ hr ha in
lemma benefiting : Summable (extract q ![v,v] : Shift (Keys 1)→ℝ) := (export_price (η:=σ) hq ![v,v] (by push_cast; simp)).summable (NNReal.coe_nonneg σ)
lemma series : design p (imp v W) = ∑' t:Tailor 1, b t * (∑ i:Site m,W i*W (i+wrap m (legLane t 1))) := by
   rw [design_long]; simp_rw [cellpack (p:=p) hr ha, ← tsum_mul_right]
   have he i j: Summable fun t:Tailor 1=> (if j=i+ wrap m (legLane t 1) then b t else 0)*(W i*W j):= by
     have hF:=benefiting (q:=q) hq v; apply Summable.mul_right _; exact Summable.congr (hF.indicator (s:= {t:Tailor 1 | j=i+wrap m (legLane t 1)})) (fun t=> by simp [Set.indicator]) 
   simp_rw [← Summable.tsum_finsetSum (fun j (hj : j∈Finset.univ) => he _ j)]; rw [← Summable.tsum_finsetSum (fun j _=>summable_sum (fun i _=> he j i))]  
   apply tsum_congr; intro t; rw [mul_sum]; apply sum_congr rfl; intro i _; simp [ite_mul]

omit instZ hr ha in
lemma line_series : Summable fun t:Tailor 1=> b t * (∑ i:Site m,W i*W (i+wrap m (legLane t 1))) := by
   let f (x:Site m):ℝ:= ∑ i:Site m,W i*W (i+x); obtain ⟨D,hD⟩:= (Set.finite_range (fun x=>‖f x‖)).bddAbove; exact Summable.of_norm_bounded ((benefiting hq v).norm.mul_right D) (fun i=> by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hD ⟨_,rfl⟩) (norm_nonneg _))
omit instZ hr ha hq
private lemma dawn (i:Keys 1)(t:Tailor 1): Quill.zen 3 (fun x:Tailor 1=>(x i:ℝ)^2) t=(t i:ℝ)^2:= by
   let p(x:Tailor 1):ℝ:=(x i:ℝ)^2
   have he (l : List (Keys 1))(h:l.length=3)(x:Tailor 1) : Quill.iterate p l x=0:= by
      match l,h with
      | [a,c,s],_=> simp only [Quill.iterate, Quill.jump,p,Pi.add_apply,arc,Pi.single_apply,Int.cast_add]; split_ifs <;> ring
   have hx:= Quill.localized (p:=p) 3 le_rfl (size t) (show ∀ l: List (Keys 1), l.length=3 → ∀ x:Tailor 1,(size x:ℝ) ≤ size t → ‖Quill.iterate p l x‖ ≤ 0 from fun l h x _=> by rw [he l h x,norm_zero]) t le_rfl
   rw [zero_mul] at hx; exact (sub_eq_zero.mp (norm_le_zero_iff.mp hx)).symm
include hq
lemma rebate_turn (hs:0<σ)(hx:softRank 3 q) : Summable b ∧ (∑' i,b i)=0∧ ∀ i:Keys 1,Summable (fun x=> b x*(x i:ℝ)^2) ∧ (∑' x,b x*(x i:ℝ)^2)=0 := by
   let v':Fin 2→α:=![v,v]; let X:Tailor 1→ℝ:= extract q v'; have ht:Rays 3 _:= hx v'; have he:Width σ C X:= export_price hq _ (by push_cast; simp); refine ⟨benefiting hq v,?_ , fun i=>?_⟩
   · have hu:= Quill.stars hs he (fun _=>1) 1 (ht.weaker (by decide : 1≤3)); simpa only [Quill.zen, Finset.sum_range_one,Quill.piece,mul_one] using hu

   have he₁ (x:Tailor 1) : X x*Quill.zen 3 (fun x=>(x i:ℝ)^2) x=b x*(x i:ℝ)^2:= congr_arg _ (dawn i x)
   exact ⟨(Quill.zen_summable hs he (fun x=>(x i:ℝ)^2) 3).of_norm.congr (fun j=> he₁ j),(tsum_congr fun j=> (he₁ j).symm).trans (Quill.stars hs he _ 3 ht)⟩
omit hq
lemma vita (V:Type)[Fintype V](x : Shift V) (i:V) : (x i).natAbs ≤ size x:= single_le_sum (f:=fun i=>(x i).natAbs) (fun _ _=> Nat.zero_le _) (mem_univ i)
include hq
-- explicit
abbrev whip (σ:ℝ) := (max 1 (3*σ⁻¹):ℝ)^3
def swell_price (σ:ℝ)(C: ℝ) := 6*(whip σ*C)
lemma swell_OK (hs:0<σ)(i:Keys 1): SumBudget (fun t:Tailor 1=> ‖b t‖*((charge (t i).natAbs:ℝ)*(↑(t i).natAbs:ℝ)^2)) (swell_price σ C):= by
   have he:=export_price (η:=σ) hq ![v,v] (by simp)
   let D:=6*whip σ
   refine budget_mono (f:=fun t:Tailor 1=> D*(Real.exp ((σ:ℝ)*size t)*‖b t‖)) ?_ (fun _=>by positivity) ?_
   · apply budget_loosen (budget_scale (show 0≤D by unfold D whip; positivity) he); unfold D swell_price; apply le_of_eq; ring
   intro t; rw [← mul_assoc D, mul_comm ‖b _‖]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
   let g := (t i).natAbs; let k:= max (1:ℝ) (3*(σ:ℝ)⁻¹); let Y:ℝ:= size t; have hu:(g:ℝ) ≤ Y:=Nat.cast_le.mpr (vita (Keys 1) t i)
   have hf : 1 ≤ k:= le_max_left ..; have hP:0<(σ:ℝ):=hs
   have ha : 1+(g:ℝ) ≤ k*Real.exp (σ/3*Y):= by
      have hb : 1+σ/3*Y ≤ Real.exp (σ/3*Y) := by rw [add_comm]; exact Real.add_one_le_exp _
      have hg:1≤k*((σ:ℝ)/3):= le_trans (le_of_eq («b»:=(3*(σ:ℝ)⁻¹)*(σ/3)) (by field_simp)) (mul_le_mul_of_nonneg_right (le_max_right ..) (by positivity))
      refine le_trans ?_ (mul_le_mul_of_nonneg_left hb (zero_le_one.trans hf)); rw [mul_add,← mul_assoc,mul_one]; apply add_le_add hf; apply hu.trans; exact le_mul_of_one_le_left (by unfold Y; positivity) hg
   have hc : (1+(g:ℝ))^3 ≤ whip σ*Real.exp ((σ:ℝ)*Y):= by refine (pow_le_pow_left₀ (by positivity) ha 3).trans_eq ?_; rw [mul_pow,← Real.exp_nat_mul]; unfold k Y whip; push_cast; congr 2; ring
   apply le_trans («b»:=6*(1+(g:ℝ))^3) _ ?_
   · unfold charge; change (((3*(2*g+1):ℕ):ℝ))*(g:ℝ)^2 ≤ _ -- edit
     push_cast; nlinarith only [Nat.cast_nonneg (α:=ℝ) g,sq_nonneg (g:ℝ)]
   unfold D; rw [mul_assoc]; gcongr
include hr ha instZ
-- economical
lemma polarized (hm:m.val=2*n) (hs:0<σ)(hx:softRank 3 q) : let f (x:Site m):= saw n (x 0); ‖design p (imp v f)‖≤ 2⁻¹*rate m*swell_price σ C:= by
   intro f; let w (t: Tailor 1):= wrap m (legLane t 1); let H t (x:Site m):= f (x+w t)- f x; let j:Keys 1:=(0,0); let g (t:Tailor 1):=(t j).natAbs; let K t:= ∑ x:Site m,(H t x^2-(g t:ℝ)^2)
   have hK (t:Tailor 1): ‖K t‖≤ rate m*((charge (g t):ℝ)*(g t:ℝ)^2):= (limited hm (t j)).trans_eq (by ring_nf; rfl)
   let f₀:= (∑ i:Site m,f i^2); let s:ℝ:= Fintype.card (Site m)
   have he t: K t=2*(f₀ - ∑ x:Site m,f x*f (x+w t))-s*((t j:ℝ)^2):= by
      have hh (x:Site m) : (f (x+w t)-f x)^2=f (x+w t)^2+f x^2-2*(f x*f (x+w t)):=by ring
      unfold K H; simp_rw [hh,sum_sub_distrib,sum_add_distrib,← mul_sum,Finset.sum_const,nsmul_eq_mul,card_univ]; rw [show ∑ x:Site m,f (x+w t)^2=f₀ from Equiv.sum_comp (Equiv.addRight (w t)) (fun x=>f x^2),show (g t:ℝ)=|((t:Tailor 1) j:ℝ)| from ?_]; rw [sq_abs]; unfold f₀ s; ring
      unfold g; rw [Nat.cast_natAbs,Int.cast_abs]
   obtain ⟨hb,h'x,hB⟩:= rebate_turn hq v hs hx
   obtain ⟨hz,h⟩:= hB j
   let Z t:=b t * K t
   have hZ: ∑' i,Z i = -2* design p (imp v f):= by
      have ht t: Z t=(2*f₀)*b t-2*(b t*∑ x:Site m,f x*f (x+w t))-s*(b t*(t j:ℝ)^2):= by unfold Z; rw [he]; ring
      have hy:= hb.mul_left (2*f₀); have hf:= (line_series hq v f).mul_left 2
      simp_rw [ht]; erw [Summable.tsum_sub (hy.sub hf) (hz.mul_left s), Summable.tsum_sub hy hf, tsum_mul_left,h'x,tsum_mul_left,tsum_mul_left,h, series hq hr ha v f]; simp only [mul_zero,zero_sub,sub_zero,neg_mul]
   have hr t: ‖Z t‖ ≤ rate m*(‖b t‖*((charge (g t):ℝ)*(g t:ℝ)^2)):= by rw [show ‖Z t‖=_ from norm_mul (b t) (K t)]; exact (mul_le_mul_of_nonneg_left (hK t) (norm_nonneg _)).trans_eq (by ring)
   have hk:=swell_OK hq v hs j; let e:= rate m; have he:0≤e:= by unfold e rate; positivity
   have hu:=budget_mono (budget_scale he hk) (fun i=>norm_nonneg (Z i)) hr; have hh:= (norm_tsum_le_tsum_norm hu.2.1).trans hu.2.2; rw [hZ,norm_mul,norm_neg] at hh; simp_rw [show ‖(2:ℝ)‖=(2:ℝ) from Real.norm_of_nonneg (by norm_num)] at hh; change _≤2⁻¹*e*_; linarith
end pole
end YM.Contacts.Model.Slope
