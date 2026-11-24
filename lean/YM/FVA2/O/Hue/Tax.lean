import YM.FVA2.O.Pad.Stamp
/-!
# Polynomial bounds under large-time evolution

`Profit`: the pricing predicate on coefficients of our local projections.
Need the `prime` (t=0 input) bounds and control of velocity of the
underlying response before obtaining this on `flash` (`paid_φ`).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Hue
open MS Function Filter Set Finset MS.Latch Job MS.Plane MeasureTheory Real Metric
open Heat LogTime IntervalFamily Koszul Tone Momentum Landau Fiddle Osc Snap Wire Signal
open Flux Book High Detect MS.Color MS.Local.Physical MS.Land Domain Convolve
open Lives O.Ward MS.City MS.Rake Outlook Tune
open scoped Topology ContDiff
variable {E F I:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
variable {G:Gauge} {P:IntervalFamily I}{j m:ℕ}{α r:ℝ}
variable {f H : I→ℝ→ E→F}{φ x:I→ℝ} {S:Scale I}
abbrev Profit (S:Scale I)(f:I→E): Prop:= paid S (fun i=> ‖f i‖) 1
variable {a b:I→E}{K:I→ℝ}
lemma prof {S:Scale I}: Profit S a↔ Bound S (fun i (_x:ℝ)=> a i) 1:= by
    refine ⟨ fun h=> Costs.scalar (paid_at h (fun _=>zero_le_one)),?_⟩; rintro p; obtain ⟨C,hC,k,hp⟩:= p.norm_cost; refine ⟨ C,hC,k,fun i=> ?_⟩; specialize hp i 0 trivial; simpa only [ Scale.full,Scale.weight_zero,mul_one ] using hp -- Pi.one
lemma Profit.plus (h: Profit S a)(he:Profit S b) : Profit S (a+b):= prof.mpr ((prof.mp h).add (prof.mp he))
lemma Profit.cash (h: Profit S K)(he:Profit S b): Profit S (fun i=> K i • b i):= prof.mpr (by convert! (prof.mp h).smul (prof.mp he) using 1; ext; simp )
lemma Profit.scalar (h:Profit S b)(c:ℝ): Profit S (c • b):= prof.mpr (Costs.L (c • ContinuousLinearMap.id ℝ E) (prof.mp h))
lemma Profit.L (h:Profit S b)(c:E→L[ℝ] F): Profit S (c∘ b):= prof.mpr ( (prof.mp h).L c )
lemma Profit.z : Profit S (0:I→E):= prof.mpr ( Costs.zero fun _ _ _=> zero_le_one )
-- backward integration§ logscale
lemma tax_h (hh:P.beg=0)(ht:Every P)(he: α+j<0)(hp:Bound P.primary ( here H ) (pays 1 α))(hd: P.Along f H j)(a:I→ ( E [×j]→L[ℝ] F ))(ha:∀ i,Tendsto (fun t=> iteratedFDeriv ℝ j (f i t) 0) atTop (𝓝 (a i))): Profit P.dawn (fun i=> a i- iteratedFDeriv ℝ j (f i 0) 0) := by
    obtain ⟨C,hC,k,hP⟩:= hp.quoted j; obtain ⟨K,hK,hV⟩:= backward_cost (b:=- (α+j)) (E:= E [×j]→L[ℝ] F) (neg_pos.mpr he) k; have hg(i:I): P.window i=Set.Ici 0:= by rw [ht,hh]; rfl
    refine ⟨ C*K,by positivity,k,fun i=>?_⟩; let A:= C* P.logPart i^k; have hL:=P.lg i; have hA: 0<A:=by unfold A; positivity
    let F (s:ℝ):= iteratedFDeriv ℝ j ( f i s ) 0; have h (b:ℝ)(hz:0≤b) : dist ( F 0 ) ( F b )≤ C*K*P.dawn.basic i^k := by
         have hw : Set.Icc 0 b⊆P.window i:= fun x hx=>(by rw [hg i]; exact hx.1)
         apply (hV 0 b A le_rfl hz hA.le F (fun u=> iteratedFDeriv ℝ j ( H i u ) 0) (fun u hu=>( hd i u (hw hu) (0:E) ).mono hw ) (fun u hu=>?_)).trans; · apply le_of_eq; simp [ A,polyExp,hh]; ring
         let v:= P.choose i u (hw (Ico_subset_Icc_self hu)); apply (hP v (0:E) trivial).trans; simp only [pays, Pi.one_apply, one_mul ]; simp only [ Scale.full, Scale.weight_zero,mul_one ]; apply le_of_eq; unfold polyExp; dsimp only [v,IntervalFamily.choose,index,t]; simp only [neg_neg,add_mul, Real.exp_add,Real.exp_nat_mul,mul_pow,A]; ring
    change ‖a i - F 0‖≤ _*1; rw [mul_one,← dist_eq_norm,dist_comm]; exact le_of_tendsto ( tendsto_const_nhds.dist (ha i) ) ((eventually_ge_atTop (0:ℝ)).mono h)
lemma tax_i (hd:P.beg=0)(hp:Bound P.dawn (fun i=> f i 0) 1) : Profit P.dawn (fun i=> iteratedFDeriv ℝ j (f i 0) 0):= by obtain ⟨C,hC,k,hk⟩:= hp.quoted j; refine ⟨ C,hC,k, fun i=>?_⟩; specialize hk i 0 trivial; simpa only [ Scale.full,Scale.weight_zero,IntervalFamily.dawn,hd, Pi.zero_apply,add_zero,exp_zero,one_pow,mul_one ] using hk
variable {X Y:Glade G I}{h u:ℤ}{w: Legs (Lane4 G)}
abbrev prime (P:IntervalFamily I)(F:Glade G I): Prop:= Latch.Lease false false P.dawn (fun i=> F i 0) 1
lemma rayB (hT:P.beg=0)(h:prime P X)(w:Wire (BH G) E QP): Bound P.dawn (fun i=> canvas X w i 0) 1:= ( h E w (fun i=>Bool.noConfusion i) (fun i=>Bool.noConfusion i) ).raise ( Cost.of_le fun i x _=> show P.dawn.length i^pitch w*1≤1 from by simp [hT] )
lemma paid_t (hT:P.beg=0)(ht:Every P)(ha:Warm X false)(hb:Warm Y false)(hx:Velocity X Y)(hs:width P Y h w.length)(hi:prime P X)(he:fieldDim wfield w+j=u)(hh:u≤h): Profit P.dawn (fun i=> flash X w.length u i w):= by
    let v:=ray w; let H(i:I):= broadW ha hb ht hx hs i; choose a ha' using (fun i:I=> H i|>.needs ℝ v (fun k=>Bool.noConfusion k) (ray_len ..) j (show fieldDim wfield v+j≤h from (by unfold v; rw [ray_dim,he]; exact hh)) 0 ); let f:=canvas X v; let U i:= iteratedFDeriv ℝ j (f i 0) 0; have hp := tax_h (f:=f) hT ht (( int_need p_gain s_gain ).mpr (show (fieldDim wfield v-h:ℤ)+j≤0 from by unfold v; rw [ray_dim]; omega)) (caption.mp ( hs ℝ v (ray_len ..) (fun i=>Bool.noConfusion i) )) (Track_now P ha hb hx v j) a ha'; change Profit _ (a-U) at hp; obtain hz : Profit P.dawn a:= by simpa only [U,sub_add_cancel] using hp.plus ( tax_i hT (rayB hT hi v) : Profit _ U )
    let L : (ℝ [×j]→L[ℝ] ℂ)→L[ℝ]ℂ:= (Nat.factorial j:ℝ)⁻¹ • ContinuousMultilinearMap.apply ℝ (fun _=>ℝ) ℂ (fun _=>1)
    have hv : ∀ i,L (a i)= flash X w.length u i w:= by intro i; exact tendsto_nhds_unique (( L.continuous.tendsto (a i) ).comp (ha' i)) (slice_torch (H i) 0 (fun p=>Bool.noConfusion p) rfl he hh) -- rank? comp fn
    exact funext hv ▸ hz.L L -- comp defeq proof
lemma paid_φ (hT:P.beg=0)(ht:Every P)(ha:Warm X false)(hb:Warm Y false)(hx:Velocity X Y)(hs:width P Y h m)(hi:prime P X)(hh:u≤h)(l:Legs (Lane4 G)): Profit P.dawn (fun i=> flash X m u i l):= by
    by_cases hr:m=l.length; swap; · unfold flash; rw [ funext (fun i=>rank_slice ( r:=m ) ( M:=col X i ) (x:=0) (v:=u) l (fun p=>Bool.noConfusion p : false = true → _) (Ne.symm hr) ) ]; exact Profit.z
    subst m; rcases lt_or_ge u (fieldDim wfield l) with p|p; · unfold flash; rw [funext (fun i:I=>slice_extra ( r:=l.length ) ( b:=false) ( M:=col X i ) (x:=0) p) ]; exact Profit.z
    exact paid_t (j:=(u-fieldDim wfield l).toNat) hT ht ha hb hx hs hi (by omega) hh
end YM.FVA2.O.Hue
