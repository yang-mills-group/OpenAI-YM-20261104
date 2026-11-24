import YM.Contacts.Lintel.Beam
namespace YM.Contacts.Lintel
set_option linter.unusedSectionVars false
open Function Set Finset Filter Metric RG Wilson Lattice Precision Exterior MeasureTheory
open Bloch Milling Milling.Steam Pulse Spine MergeProof Milling.Forge Laurent Stationary Matrix Work.F05
open Milling.Garf Form House PertExtension.Series Tree Larch FreeResolvent PhysicalNext.RankCovariance
open PertExtension.Chart Radial
open scoped Topology BigOperators Matrix Classical NNReal ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {G:Gauge}{c f m: Side}{α:ℕ→Type}{n k:ℕ}
variable {V X Y E:Type}[NormedAddCommGroup V][NormedSpace ℝ V][FiniteDimensional ℝ V]
   [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable {t:E} {a b:E→ ℝ}
namespace Crag
open Wire
open Tested Ion
local notation "ζ" => (ℝ × E)
def margin (F:ℝ × E→ℝ):ℝ×E→ℝ:= fun x=> F x-F (x.1,0)
variable {T:ℝ × E→ℝ}{K J:E→ℝ}
def score (K J:E→ℝ)(x:ℝ×E):= conjunct K 0 x+conjunct J 2 x
theorem score_s (h:AnalyticAt ℝ K 0)(he:AnalyticAt ℝ J 0): AnalyticAt ℝ (score K J) 0:= (conjunct_ana h 0).add (conjunct_ana he 2)
theorem score_station (h: AnalyticAt ℝ K 0)(he:AnalyticAt ℝ J 0)(hp:Rays 2 K): Rays 2 (score K J):= by
    refine (jet_bridge (score_s h he)).2 fun x i hi=> ?_; change jet (conjunct K 0+_) i x=0; rw [serif (conjunct_ana h _) _ (conjunct_ana he _), joint K i _ _ h, joint J i _ _ he]; simp only [if_pos (Nat.zero_le _), if_neg (not_le.mpr hi),pow_zero, one_mul,Nat.sub_zero,add_zero]; exact (jet_bridge h).1 hp x.2 _ hi
lemma score_pay (K J:E→ℝ)(x:E){t:ℝ}(ht:t≠0): Milling.sample (score K J) (1,x) t=K (t•x)/t^2+J (t•x):=by unfold score Milling.sample conjunct; simp only [Prod.smul_snd,Prod.smul_fst,pow_zero,one_mul,smul_eq_mul,mul_one]; field_simp
private def chill : ζ→L[ℝ]ζ:= (ContinuousLinearMap.fst ℝ ℝ E).prod 0
lemma drop_actor (T:ℝ×E→ℝ) : margin T= T-T∘ (chill:ζ→ζ):= rfl
lemma margin_s {T:ℝ×E→ℝ} (h:AnalyticAt ℝ T 0) : AnalyticAt ℝ (margin T) 0:=h.sub (Forge.starts _ h (chill (E:=E)))
lemma margin_zero (T:ζ→ℝ)(x:E): margin T (0,0)=0:= sub_self _
local notation "φ" => Tested.germ
section rates
variable {f g:ℝ→ℝ}{a b:ℝ}
lemma bills_near (h:Bill n f)(he: f=ᶠ[φ] g): Bill n g:= by obtain ⟨c,hc,h⟩:=h; exact ⟨c,hc,(he.and h).mono fun t h=>by rw [← h.1]; exact h.2⟩
lemma bills_mul (hf:Bill n f)(hg:Bill k g): Bill (n+k) (f*g):= by obtain ⟨c,hc,h⟩:=hf; obtain ⟨d,hd,H⟩:=hg; refine ⟨_,mul_nonneg hc hd,( h.and (H.and eventually_pos)).mono fun t ht=>?_⟩; obtain ⟨hx,hy,hz⟩:=ht; rw [Pi.mul_apply,norm_mul,pow_add,mul_mul_mul_comm]; gcongr -- test
lemma bills_const (b:ℝ): Bill 0 (fun _=>b):= ⟨_,norm_nonneg b,Eventually.of_forall fun t=>by simp⟩
lemma bills_tend (h:Tendsto f φ (𝓝 a)): Bill 0 f:= ⟨‖a‖+1,by positivity,(h.norm.eventually_le_const (lt_add_one _)).mono fun _ h=>by simp only [pow_zero,mul_one]; exact h⟩
lemma bills_mul_l (hf:Bill 0 f)(hg:Bill n g): Bill n (fun x=>f x*g x):= Nat.zero_add n ▸ (bills_mul hf hg) -- defeq maybe
lemma bills_sub (hf:Bill n f)(hg:Bill n g): Bill n (fun x=> f x-g x):= by change Bill n (f-g); simpa only [← sub_eq_add_neg] using (show Bill n (f + -g) from bill_add hf (bill_neg hg)) --
lemma zero_atom {g: E→ℝ}(h:AnalyticAt ℝ g 0)(x:E) : Bill 1 (fun t=>g (t•x)-g 0) := by obtain ⟨c,hc,h⟩:= leaf h 0 x; exact ⟨c,hc,(by simpa only [jet_zero,Zone.eval,Nat.zero_add, Finset.sum_range_one,pow_zero,one_smul] using h)⟩ -- orientation `h` binder
private lemma exponent_book (h:Rays 2 g')(x:E): Bill 0 (fun t=> Real.exp (Milling.sample g' x t)) := by
    obtain ⟨c,hc,h⟩:= limited h x; refine ⟨_,(Real.exp_pos c).le, h.mono fun t h=>?_⟩; rw [Real.norm_of_nonneg (Real.exp_pos _).le,pow_zero,mul_one]; exact Real.exp_le_exp.mpr ((le_abs_self (Milling.sample g' x t)).trans h)
lemma chill_anchor (x:E)(p:ℝ)(F:ζ→ℝ): Milling.sample (F∘chill) (1,x) p=Milling.sample F (1,0) p:=by simp [Milling.sample,chill]
-- Pay after ratio. choose q once
lemma readRatio {x:E}{j y:ℝ} (hb:b>0) (h:AnalyticAt ℝ J 0)(hp: Rays 2 K)
    (hf:Bill 3 (fun t=> f t-b*Real.exp (-Milling.sample T (1,x) t))) (he: Bill 3 (fun t=> Real.exp (Milling.sample K x t)*f t - j*Real.exp (-J (t•x))-t^2*y)) : Bill 3 (fun t=> Real.exp (-Milling.sample (T - score K J) (1,x) t) - (j+t^2*y*Real.exp (J 0))/b) := by
   let G (t:ℝ):=Real.exp (Milling.sample K x t); let A (t:ℝ):=Real.exp (J (t•x)); let F':= T - score K J; let H (t:ℝ):=Real.exp (-Milling.sample F' (1,x) t); let v (t:ℝ):= Real.exp (-J (t•x)); let w:=Real.exp (J 0)
   have hA: AnalyticAt ℝ (Real.exp ∘ J) 0:= (h.contDiffAt.exp).analyticAt
   have h': Bill 3 (fun t=> G t*(b*Real.exp (-Milling.sample T (1,x) t))-j*v t-t^2*y):= by convert (bills_sub he (bills_mul_l (exponent_book hp x) hf)) using 1; ext1 t; unfold G v; ring
   let r t:= t^2*y*(A t-w); have hr: Bill 3 r := bills_mul (show Bill 2 (fun t:ℝ=> t^2*y) from Tested.bill_mon y _ le_rfl) (show Bill 1 (fun t=> A t-w) from zero_atom hA x)
   have hx:=bill_add (bills_mul_l (bills_tend (f:=A) (hA.continuousAt.tendsto.comp ((along x).mono_left (nhdsGT_le_nhdsNE _)))) h') hr; refine bills_near (bills_mul_l (bills_const b⁻¹) hx) (eventually_pos.mono fun t ht=>?_ )
   have ht' : A t*G t*Real.exp (-Milling.sample T (1,x) t)=H t:= by unfold A G H F'; rw [← Real.exp_add,← Real.exp_add]; congr 1; rw [show Milling.sample (T-score K J) _ _=Milling.sample T (1,x) t-Milling.sample (score K J) (1,x) t from (by unfold Milling.sample; simp only [Pi.sub_apply,sub_div]),score_pay _ _ _ ht.ne']; unfold Milling.sample; ring
   have hv : A t*v t=1:=by unfold A v; rw [← Real.exp_add,add_neg_cancel,Real.exp_zero]
   change b⁻¹*(A t*(G t*(b*Real.exp _)- j*v t - t^2*y)+r t) = H t- (j + t^2*y*w)/b; unfold r; field_simp; let N:= Real.exp (-Milling.sample T (1,x) t); have hu := congr_arg (j*·) hv; have hE : A t*(G t*(b*N)- j*v t -t^2*y)= b*H t - j -(t^2*y)*A t:= by unfold N; rw [← ht']; linarith only [show j*(A t*v t)=j from hu.trans (mul_one j)];
   unfold N at hE; linarith only [hE]
-- General? layout fix
structure Tide (K J:E→ℝ)(M S:E×V→ℝ):Prop where
    classA : AnalyticAt ℝ K 0
    thermal : AnalyticAt ℝ J 0
    amp : AnalyticAt ℝ S 0
    fA : AnalyticAt ℝ M 0
    classZero : Rays 2 K
    within : ∀ᶠ x:E in 𝓝 0,M (x,0)=0 ∧ fderiv ℝ (fun y:V=> M (x,y)) 0=0
    rise: ∃ c> (0:ℝ), ∀ v,c*‖v‖^2≤ radial M (0,v)
-- differ at x vs 0
lemma signs_off (h:AnalyticAt ℝ T 0)(he:Rays 2 T){u:ℝ→ℝ} (hv:∀ x:E, Bill 3 (fun t:ℝ=>Real.exp (-Milling.sample T (1,x) t)-u t)) : Rays 5 (margin T):= by
   refine benchPitch (margin_s h) (fun x=> marker (margin_s h) _ ?_); apply sample_cost (g:=T ∘ chill) he (merkin h he _ ((chill (E:=E)).analyticAt _) (map_zero _)) (1,x) 2; convert bills_sub (hv x) (hv 0) using 1; ext t; rw [chill_anchor]; ring
end rates
variable {I:Type} [Fintype I]
section
variable [MeasurableSpace E][BorelSpace E][MeasurableSpace V][BorelSpace V]
    (μ:Measure V)[μ.IsNegInvariant][μ.HasTemperateGrowth]
variable {B: ℝ × E→(I→ G.El)→ℝ} {M S:E×V→ℝ}{j b:ℝ}
structure Draws (K:E→ℝ)(M S:E×V→ℝ)(B:ℝ × E→ (I→ G.El)→ℝ): Prop where
    draws (x:E)(U:Set (I→G.El))(hU:U∈𝓝 1):∃ q>0,∀ r∈Ioo (0:ℝ) q,∃ Z:ℝ→Set (I→G.El),∃ P∈𝓝 (1:(I→G.El)),∀ᶠ t in Tested.germ, MeasurableSet (Z t) ∧ P ⊆ Z t ∧ Z t ⊆ U ∧ beach B (Z t) t x= Real.exp (-Milling.sample K x t)*ash μ S M t (disc t r) x
include μ
theorem quota (h:Tide K J M S)(hz:∀ᶠ x:E in 𝓝 0, S (x,0)*(∫ y,Real.exp (-radial M (x,y)) ∂μ)= j*Real.exp (-J x))(he:AnalyticAt ℝ T 0)(hk:Rays 2 T) (hp:Draws μ K M S B)(hh:Sight B T b 2): Rays 5 (margin (T-score K J)):= by
   let P:=T-score K J; obtain ⟨c,hc,H⟩:=h.rise; obtain ⟨p,hZ⟩:=radial_earn μ h.fA h.within h.amp hc H; let u (t:ℝ):=(j+t^2*p*Real.exp (J 0))/b; apply signs_off (u:=u) (he.sub (score_s h.classA h.thermal)) (hk.sub (score_station h.classA h.thermal h.classZero)); intro x; obtain ⟨s,hs,hQ⟩:= hZ ‖x‖; obtain ⟨U,hU,hK⟩:= hh.weight ‖x‖; obtain ⟨q,hq,hT⟩:= hp.draws x _ hU; let r:= min s q/2; have hr:0<r:=half_pos (lt_min hs hq); have hv:r< min s q:= half_lt_self (lt_min hs hq); obtain ⟨Y,W,hW,hC⟩:= hT r ⟨hr,(hv.trans_le (min_le_right ..))⟩; obtain ⟨D,hD,hF⟩:= hK _ hW; let f t:= beach B (Y t) t x; have hx:x∈closedBall 0 ‖x‖:= mem_closedBall_zero_iff.mpr le_rfl
   refine readRatio (f:=f) hh.nz h.thermal h.classZero ⟨D,hD, (hC.and hF).mono fun t ht=> ht.2 x hx (Y t) ht.1.1 ht.1.2.2.1 ht.1.2.1⟩ (bills_near (hQ _ hr (hv.trans_le (min_le_left ..)) x hx) ?_); filter_upwards [(along x).eventually hz|>.filter_mono (nhdsGT_le_nhdsNE _),hC] with t hz hC; rw [hz,show f t=_ from hC.2.2.2, ← mul_assoc, ← Real.exp_add,add_neg_cancel,Real.exp_zero,one_mul]
end
end Crag
end
end YM.Contacts.Lintel
