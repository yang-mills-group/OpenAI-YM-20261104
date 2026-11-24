import YM.Contacts.Model.Sundial
/-! Recover small-f price on the aggregate jets, despite lack of budget on simultaneous values at different periods. Symbols before flags. -/
noncomputable section
namespace YM.Contacts.Model
open Function Lattice Finset Filter Set PhysicalNext.Repeat Pressure Wilson MeasureTheory RG
open Slide (Stars)
open Trio (froth Mirrors Offer)
open AnalyticBridge VerifiedReset Push.AbsoluteSums Animals YM.Stationary Milling PertExtension.Series Exterior Precision Ion
open Pulse Spine Garf Steam Bloch Radial House Lumen Metric Push.Uniform Kale
open scoped Topology NNReal InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{n m c:Side}{k w r z ℓ i j:ℕ}
namespace Province
open Slope Arbor Lintel.Plata ConnectedActivityE6 Next.Fluctuations Blaze Sienna
open scoped Interval
open Boulevard (actual)
open Barrage.Reserve
namespace Costing
variable {A H Z t C Λ I μ a d r:ℝ}{S:ℝ≥0}{v:ℕ}{B:BudgetPoint}{X:G.ColorIndex}{P:Bed}{L:Side}
variable {f g : ℝ→ℝ}{p: ℝ→ℕ}
lemma ownHat (x:ℝ): betaF G x 1=x:=by simp [betaF]
lemma power (a:ℝ): Rate G 1 a (fun x=> x^a):=by have h: Rate G 1 a (fun x=> betaF G x 1 ^ a):= Rate.power; simpa only [ownHat] using! h
lemma zero (a:ℝ) : Rate G L a (fun _=>0) := by
   intro b hb; filter_upwards [Delay.shift_pos G L] with x hx; simp only [abs_zero]; positivity
lemma faster (hr:Rate G 1 r f) (hx:r<d) : ∀ᶠ x in atTop, |f x|≤x^d:= by simpa only [ownHat] using! hr d hx
abbrev Flat (G:Gauge)(f:ℝ→ℝ):= Rate G 1 0 f -- this word below means subpowers, not infinity falt spelling
lemma joinPower (h:Rate G L r f)(hh:Rate G L a g)(he:r+a=d): Rate G L d (fun x=> f x*g x):=he ▸ h.mul hh
lemma joins (h:Flat G f)(hh:Flat G g): Flat G (fun x=> f x*g x):= joinPower h hh (by norm_num)
lemma raised (h:Flat G f)(k:ℕ): Flat G (fun x=> f x^k):= by simpa only [zero_mul] using! h.pow k
lemma absolute (h:Rate G L a f): Rate G L a (fun x=>|f x|):= by exact h.compare (Eventually.of_forall fun x=>le_of_eq (abs_abs _))
lemma tribe {α:Type}(s:Finset α)(f:α→ℝ→ℝ)(h:∀ i∈s,Rate G 1 r (f i)): Rate G 1 r (fun x=>∑ i∈s,f i x):= by
   induction s using Finset.induction with| empty=> simpa only [Finset.sum_empty] using zero r|insert i s hi ih=>simp_rw [Finset.sum_insert hi]; exact (h i (mem_insert_self _ _)).add (ih (fun i hi=> h i (mem_insert_of_mem hi)))
lemma cardLand (m:Side): (Fintype.card (Site m):ℝ)=(m.val:ℝ)^4:=by simp [Site,Four,Per,Axis]
-- subpower costs for analytic model.
lemma wideQ : Flat G fun x=> (Province.width (radiusB x):ℝ) := by unfold Province.width; push_cast; exact Rate.radius_price.mul_left _
lemma travel {k:ℕ}{a:ℝ→ℕ}(hA:Flat G fun x=> ((a x:ℕ):ℝ)) : Flat G fun x=> travelCost G k (4*a x) Z := by
   unfold travelCost composeCost; push_cast; exact ((raised (((Rate.const 1).add (Rate.mul_left ((Rate.const 1).add (hA.mul_left _)) _))) k).mul_left _|>.mul_left _).mul_right _ -- factor order
lemma window_a {u:ℝ→ℕ} (k j:ℕ)(h:Flat G f) (hp:Flat G fun x=>(u x:ℝ)): Flat G fun x=> arcPrice G (u x) k j Z (f x):= by
   apply joins h; apply tribe; intro c hc; have ha:Flat G fun x=>arborPrice G (u x) k Z:= by
      let v:=fun x :ℝ=>travelCost G k (4*u x) Z; have hh:Flat G v:= travel hp; exact joins (((hh.mul_left _).mul_right _).mul_left _) hh
   let v:= fun x:ℝ=>composeCost k (Logprice G k) (arborPrice G (u x) k Z)
   have h':Flat G v:= Rate.mul_left (raised ((Rate.const 1).add ha) k) _ -- missed factor yes factoring `(n!*K) *`
   exact joins (f:=fun x:ℝ=> ((u x:ℝ)^4*(Fintype.card (Loc G 1):ℝ))^c) (raised ((raised hp 4).mul_right _) c) (raised ((Rate.const 1).add (absolute (h'.mul_left _))) c)
lemma lobby (p:Clip) (h:Flat G f): Flat G fun x=> sumFee G p Z μ C (f x) k:= by unfold sumFee; apply Rate.add _ (Rate.const _); exact (Rate.const _).add (absolute (h.mul_right _))
lemma oath (p:Clip)(u:ℝ→ℕ) (h:Flat G f)(hp:Flat G fun x=>(u x:ℝ))(hr:Flat G g): Flat G fun x=> tollP G p (u x) z k (f x) Z μ C (g x):= Rate.add (window_a k z h hp) (joins (raised hp 4) (lobby p hr))
lemma summitArc (p:Clip)(h:Flat G f)(hr:Flat G g): Flat G fun x=> upCard G p (Province.width (radiusB x)) z k (f x) Z μ C (g x):= tribe Finset.univ (fun (i:Stars) x=> |Slide.ray i| * tollP G p (Province.width (radiusB x)) z k (f x) Z μ C (g x)) (fun _ _=> (oath p _ h wideQ hr).mul_left _)
lemma lushPrice (G:Gauge): Flat G lush:= by
    refine (Rate.radius_price (G:=G) (L:=1)).compare ?_; filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 10] with x hx; rw [abs_of_pos (lush_pos x),abs_of_nonneg (Nat.cast_nonneg _)]; apply le_trans _ (Nat.le_ceil _); unfold lush; rw [max_def]; split; next ha=> have ht := Real.log_le_sub_one_of_pos (show 0<Real.log x by linarith); nlinarith
    nlinarith
lemma ample : ∀ᶠ x in atTop,20 ≤ radiusB x:= Work.E01.radiusB_tendsto.eventually_ge_atTop _
lemma tileRate (i:Stars): Flat G fun x=> ((tiles (radiusB x) i).val:ℝ):= wideQ.compare (v:=fun x=> ((tiles (radiusB x) i).val:ℝ)) (ample.mono fun x hx=> by simp; exact_mod_cast tile_cap hx i)
lemma longpole (b:ℝ) : ∀ᶠ x in atTop, b* lush x ≤ Real.log x:= by
   by_cases hb:0 < b; swap; · exact (Real.tendsto_log_atTop.eventually_ge_atTop 1).mono fun x hx=> le_trans (mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hb) (lush_pos _).le) (by linarith)
   have hl := Real.isLittleO_log_id_atTop.def (show 0 <(2*b)⁻¹ by positivity)
   filter_upwards [Real.tendsto_log_atTop.eventually hl,Real.tendsto_log_atTop.eventually_ge_atTop (4*b), (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1] with x hx hv ht; simp only [Real.norm_eq_abs,id_eq] at hx; change 1 ≤ Real.log (Real.log x) at ht; rw [abs_of_pos (by linarith only [hv,hb]: 0<Real.log x), abs_of_pos (by linarith only [ht]:0<Real.log (Real.log x)),inv_mul_eq_div] at hx; have hx:=(le_div_iff₀ (show 0<2*b by positivity)).1 hx; unfold lush; rw [max_eq_right (by linarith only [ht]:0≤Real.log (Real.log x))]; nlinarith
lemma coneCost (a:ℝ) : Rate G 1 a fun x=>Real.exp (- (narrow x:ℝ)*aperture (radiusB x)) := by
    intro d hd; let c:= max 1 (-d); have hc:0<c:= zero_lt_one.trans_le (le_max_left ..);
    filter_upwards [ample,longpole (5*c), Real.tendsto_log_atTop.eventually_ge_atTop 10,eventually_ge_atTop (1:ℝ)] with x hx hp hr hX; let a' :=aperture (radiusB x);
    have hh: (Real.log x)^2 ≤ 5*(a':ℝ) := by
       have hx: (Real.log x)^2 ≤ radiusB x:= Nat.le_ceil _; have ho:100 ≤ radiusB x:= by have ht: (100:ℝ)≤ radiusB x:=(by nlinarith only [hx,hr]); exact_mod_cast ht
       exact hx.trans (by exact_mod_cast (by unfold a' aperture; omega : radiusB x ≤ 5 * a'))
    rw [ownHat,abs_of_pos (Real.exp_pos _),Real.rpow_def_of_pos (zero_lt_one.trans_le hX)]; apply Real.exp_le_exp.mpr; change -(lush x)⁻¹ *(a':ℝ) ≤ _; have hX:=lush_pos x; rw [neg_mul,neg_le,inv_mul_eq_div]; apply (le_div_iff₀ hX).2; nlinarith only [hh,hp,hX,mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (show -d ≤ c from le_max_right ..) hX.le) (by linarith:0≤Real.log x), mul_le_mul_of_nonneg_left hp (by linarith:0≤Real.log x)] -- nlin
lemma volcanic (v:ℝ) (h:0<μ): Rate G 1 v fun x=> Model.pole μ (aperture (radiusB x)+1):= by
    refine (coneCost v).compare ?_; filter_upwards [ lush_matures.eventually_ge_atTop (2/μ)] with x hx; simp_rw [Model.pole, abs_of_pos (Real.exp_pos _)]; apply Real.exp_le_exp.mpr; have he:μ/2≥(lush x)⁻¹:= by apply (inv_le_comm₀ (lush_pos _) (half_pos h)).2; rwa [inv_div] -- wrong
    change _ ≤ -(lush x)⁻¹*_; push_cast; nlinarith only [he,h,mul_le_mul_of_nonneg_right he (Nat.cast_nonneg (aperture (radiusB x)))]
lemma surrender (p:Clip)(hv:0<μ)(h:Flat G f)(he:Flat G g): Rate G 1 r fun x=> brinks G (tiles (radiusB x)) p Z μ I (g x) (f x) (narrow x) (aperture (radiusB x)) k j:= by
    have hB:Rate G 1 r fun x=> Real.exp (- (narrow x:ℝ)*aperture (radiusB x))*f x := joinPower (coneCost r) h (by ring)
    let y x:= sumFee G p (outerCost G j Z) μ I (g x) j; have hh:Flat G y:=lobby p he; have hp:Rate G 1 r fun x=> Model.pole μ (aperture (radiusB x)+1) * y x := joinPower (volcanic r hv) hh (by ring); refine Rate.add (((hB.mul_left _).mul_left _).add hp) (tribe _ _ (fun i _=>Rate.mul_left ?_ _))
    unfold inkjet; let m x:=(tiles (radiusB x) i); have he(t:Side) : (↑(Fintype.card (Lines G t 1)):ℝ)=(t.val:ℝ)^4 * (Fintype.card (Loc G 1):ℝ):=by rw [show Fintype.card (Lines G t 1)= _ from Fintype.card_prod ..,Nat.cast_mul,cardLand] -- explicit
    simp_rw [cardLand,he]; exact Rate.add ((joinPower ((raised (tileRate i) 4).mul_right _) hB (by ring)).mul_left _) (joinPower (raised (tileRate i) 4) hp (by ring))
lemma temp_cost (G:Gauge) : Rate G 1 (-(1/2)) temp := by convert Rate.flame (G:=G) (L:=1) using 1; ext v; rw [fiery, ownHat]
lemma thermometer : Rate G 1 1 (fun x=> (Pressure.temp x^2)⁻¹):= by
    refine (power (G:=G) 1).compare ?_; filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx; have hw:0<Pressure.temp x:= by unfold temp; positivity
    rw [abs_of_pos (inv_pos.mpr (sq_pos_of_pos hw)), Real.rpow_one,abs_of_pos hx]; apply (inv_le_comm₀ (sq_pos_of_pos hw) hx).2; unfold temp; rw [mul_pow,inv_pow,Real.sq_sqrt hx.le]; exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ (Real.one_le_exp (sq_nonneg _)))
def shade (order power:ℕ)(x P:ℝ) := (Push.Local.turnCost order power) * ∑ i:Stars, |Slide.ray i| * ((2^order*((1+(radiusB x:ℝ))^(power*order))) * (Boulevard.ticket order P))
def bank (G:Gauge)(t:ℝ)(a P : ℕ):ℝ:= (2:ℝ)⁻¹* (Fintype.card PlaqAxes:ℝ)*((pairingCost G.Color a *colorBill G 4 P a ^2)* t^2)
lemma equalYear (x v:ℝ)(B:BudgetPoint): year B (radiusB x) v= shade B.order B.power x v:=rfl
lemma pleasant (x:Stage) (h : Rate G 1 a f): Rate G 1 a (fun y=> shade x.order x.power y (f y)):= by
    refine (tribe _ _ (r:=a) (fun i _=> ?_)).mul_left _; unfold Boulevard.ticket; exact (joinPower ((raised ((Rate.const 1|>.add (Rate.radius_price))) (x.power*x.order)).mul_left _) ((h.mul_left _).mul_right _) (by ring)).mul_left |Slide.ray i|
lemma pleasantBank (x:Stage)(G : Gauge) : Rate G 1 0 (fun y=> bank G (temp y) x.order x.power):= by
   have he: Flat G temp:= (temp_cost G).weaken (by linarith); exact (raised he 2|>.mul_left _).mul_left _
variable (p:Stage) (k)
def shard (p:Stage)(k i:ℕ)(x:ℝ) (G:Gauge)(C Z Λ:ℝ) := shade p.order p.power x (tollP G p.clip (Province.width (radiusB x)) (k+3) p.order C (holdOn p.order (outerCost G p.order Z)) p.width p.paths Λ * x^(vow* Arbor.hero i))
lemma pieces (x:ℝ)(hv:0<x) (B:BudgetPoint) (hh:B.order=p.order)(hx:B.power=p.power): unitSize G (eaves G 1 x) B p.clip (radiusB x) k C Z p.width p.paths Λ i= shard p k i x G C Z Λ:= by unfold unitSize; rw [equalYear,hh,hx]; unfold shard eaves; simp only [ownHat]; rw [ Real.rpow_mul hv.le]; rw [Real.rpow_natCast]
lemma frequency (h:Flat G f)(hF:Flat G g): Rate G 1 (vow*hero i) (fun x=> shard p k i x G (f x) Z (g x)):= pleasant p (joinPower (oath p.clip _ h wideQ hF) (power _) (by ring))
def cliff (k:ℕ)(x:ℝ):= 1+ Nat.ceil (x^k)
def scan (k:ℕ)(x:ℝ): Side := ⟨2*cliff k x, by unfold cliff; omega⟩
lemma cliffRate (k:ℕ): Rate G 1 k (fun x=> (cliff k x:ℝ)):= by
    refine Rate.compare (w:=fun x=> (1+x^(k:ℝ))+1) (by apply Rate.add _ ((Rate.const 1).weaken (Nat.cast_nonneg _)); exact (((Rate.const 1).weaken (Nat.cast_nonneg _)).add (power _))) ?_; filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx; unfold cliff; rw [abs_of_nonneg (Nat.cast_nonneg _), Real.rpow_natCast,abs_of_pos (by positivity)]; push_cast; exact add_assoc (1:ℝ) (x^k) 1 ▸ add_le_add_right (Nat.ceil_lt_add_one (pow_nonneg hx.le k)).le _
lemma inverseRate (k:ℕ): Rate G 1 (-k) (fun x=> (cliff k x:ℝ)⁻¹):= by
    apply Rate.compare (power (-k)); filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx; have he:0<x^k:= pow_pos hx k; have ht : x^k ≤ (cliff k x:ℝ):= (Nat.le_ceil _).trans (Nat.cast_le.mpr (Nat.le_add_left ..)); rw [abs_of_pos (inv_pos.mpr (he.trans_le ht)), Real.rpow_neg hx.le,Real.rpow_natCast,abs_of_pos (inv_pos.mpr he)]; exact inv_anti₀ he ht
end Costing
end Province
end YM.Contacts.Model
