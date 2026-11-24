import YM.Contacts.Junction.Gorge
/-! # Welding horizon.Broker. Uses loyalty.Assurance.Aperture all e appropriate. 
 budget translated normalized precision. Deliver with stamped-over-p loss.Polygon. -/
noncomputable section
namespace YM.Contacts.Junction
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
open Function Filter Set Finset Metric Lattice RG Gauge Pressure Wilson PertExtension.Series MeasureTheory
open Radial Precision Matrix PhysicalNext.Repeat Bid Tree Tested PertExtension.Chart Lapis Milling
open YM.Stationary Milling.Forge Exterior Push.Uniform ConnectedActivityE6 Blaze Shield Poll Next.SectorChange Fare Model.Arbor
open scoped Topology ContDiff Pointwise BigOperators Matrix.Norms.Frobenius Classical NNReal
variable {G:Gauge} {P : ChartRatio G} {σ C e v d t K τ ω' s a R:ℝ}{n k j r i q:ℕ}
namespace Provision
open Ion House Lintel Lintel.Angle Cove Model Province.Costing Lumen Pulse Spine Steam
open Milling.Garf Loom Loom.Patch Meter Capture Buyer Push Current Milling.Spark
open Sienna Lantern Planned.JetPort Dew Uniform StagePort
open Push.AbsoluteSums SectorMeasure Presented Next.Fluctuations Next.Fluctuations.Sector Token
variable {U:Teller G} {L:Side} {M:Uniform.ChartPrices}{X:G.ColorIndex} {Φ:ℕ→StagePort G U P X k L σ C M n}
local notation "ι" => StagePort.dew ∘ Φ
local notation "E" => (fun i=> Dew.X (ι i))
local notation "Y" => (fun i=> Dew.Y (ι i))
local notation "μ" => (fun i=>StagePort.μ (Φ i))
local notation "γ" => γC (ι)
variable {N:Meter}{Q:ℝ→ℝ}
section measure
variable {β:Type}[NormedAddCommGroup β][NormedSpace ℝ β]
def morph (p:ℝ) : β→L[ℝ] β:= p • ContinuousLinearMap.id ℝ _
lemma slopes (hp:0 ≤ s) : ‖morph (β:=β) s‖≤ s:= (by unfold morph; rw [norm_smul,Real.norm_of_nonneg hp]; exact mul_le_of_le_one_right hp (ContinuousLinearMap.norm_id_le ..))
lemma flash {x:β}{u:β→ℝ}(h : Brush n t 1 u x)(p:ℝ)(_hp:0≤p)(hC:‖u x‖≤p) : Brush n (t+p) 1 (fun y=>u y-u x) x:= h.separating ((Brush.certified zero_le_one _).climb hC le_rfl) -- p hp unused
end measure
namespace Travel
open Loom.Patch
variable (p:Travel N Q Φ)(hk:2≤k)(hn:k≤n)(hG:G.Simple)(hp:LocalRatio P)(hd:0<d)
local notation "V" => (summitK Φ (d/2))
local notation "tx" => (StagePort.flag ∘ Φ)
local notation "u" => (Dew.β ∘ StagePort.dew ∘ Φ)
local notation "P₀" => (Frame.Bank (fun i=> (Φ i).dew.X) (fun _=>1))
local notation "X₁" => Frame.Port (fun i=> (Φ i).dew.X) (fun _=>1)
abbrev MeterCoat (Φ:ℕ→StagePort G U P X k L σ C M n) (i:ℕ) : (Φ i).dew.X →L[ℝ] (Φ i).dew.X:= morph ( (Φ i).flag)
local notation "L'" => MeterCoat Φ
abbrev primaryP (Φ:ℕ→StagePort G U P X k L σ C M n) (d:ℝ)(i:ℕ)(x:(Φ i).dew.X) := capT Φ d i ((Φ i).flag • x)
-- deliver.Ao. choose parameter version safe.N
include p hp hk hG hd hn
lemma reportD : N.Funds (fun i b=> let p:=Φ i; ∀ x∈P₀ i, Brush (n+3) b 1 (fun y=> Real.log (p.dream (p.flag • y))-Real.log (p.dream (p.flag • x))) x) 1:= by
    let k i:= Dew.X (ι i); let C i:= u i; let f(i:ℕ) x:= Dew.℘ (ι i) (tx i • x); let g (i) x:=(u i)*f i x; let S (i:ℕ):= Dew.Q (ι i); let H:= Frame.Port S (N.pow stashp)
    let L (i:ℕ)(x:k i):S i:= ((0,tx i • x),0); have hv: ∀ᶠ i in atTop, f i=fun x=> skel (Φ i).bench 3 (L i x) := by
       filter_upwards [p.flowFee hk hG hp hn] with i hi; ext x; rw [hi.2.2]; change _= f i x+ Junction.gram (Φ i).dew.B _ 0; simp [Junction.gram]
    have hs : Direct N (n+3) fit 1 L:= Current.polar (A:=fun i=> ℝ × k i) (Current.polar Budget.zero ( (show Direct N (n+3) fit 1 (fun i (x:k i)=> tx i • x) from Arms.weighted (Current.meetP (Meter.Rush.settle 1) le_rfl) p.fC.2 (zero_add  _)))) Budget.zero -- syntax adapt metavars.Starter.N.Pr
    have hh := p.presentFee hk hG hp hn; have h':Direct N (n+3) 0 1 f:= Arms.reveal (Loom.Budget.skew (w:=fun i=>(Φ i).bench) (j:=3) hs (by norm_num [fit]) (fun i hi=> Root.worth hh.1 Pouch.canon (by omega))) (hv.mono fun i hi j=> Eventually.of_forall fun x=> congr_fun hi x) le_rfl le_rfl; have he:= Arms.weighted (f:=u) h' (volume_count p.dawn p.scale p.plaza p.ferry|>.2.1) (zero_add _); obtain ⟨a,ha,H⟩:= (show Direct N (n+3) 1 1 g from he).cap;
    refine ⟨_,ha.blend ha,(p.dawn.and H).mono (fun i hi=> ⟨add_nonneg hi.2.1 hi.2.1,fun x hx=>?_⟩)⟩; let A:= Φ i;  have hj:= hi.2.2 ⟨_,hx⟩; have hk: Brush (n+3) (a i) 1 (g i) x:= hj; have h y : Real.log (A.dream (A.flag • y))= Real.log A.grader - g i y:= by
        let H:=A.grader; have hp : 0<A.dream (A.flag • y):= StagePort.matter hi.1 hp _; have he:H≠0:= by rintro he; unfold StagePort.dream at hp; rw [show A.grader=0 from he,zero_mul] at hp; exact lt_irrefl _ hp
        unfold StagePort.dream; rw [Real.log_mul he (Real.exp_pos _).ne', Real.log_exp]; change _= Real.log _ - (u i*_); rw [neg_mul]; rfl
    exact ((flash hk _ hi.2.1 hk.bound).opposite).shimmy (Eventually.of_forall (fun y=>by change Real.log (A.dream (A.flag • y))-Real.log (A.dream (A.flag • x))= -(g i y-g i x); erw [h y,h x]; ring))
lemma pocketSum : Direct N (n+3) 0 1 (logS V) := by
    let a:ℝ:= -1/6; have ha:Capture.race<a:=by norm_num [Capture.race,a]
    have hi:a<0:=by norm_num [a]
    let l(i:ℝ):= Real.log (i+1); have hh:AnalyticAt ℝ l 0:=(analyticAt_id.add analyticAt_const).log (by norm_num); have hp':= Capture.sees (p.heard hG hk hn hp (half_pos hd) ha hi) l hh (q:=a/2) (by linarith) (by linarith); apply Arms.cheaper _ hp'; funext x i y; exact congr_arg Real.log (sub_add_cancel (V x y) (1:ℝ)) -- congr orientation
lemma quouch (he:e<0): let q:=n+2; N.Funds (fun i b=> ∀ x∈Frame.Bank (fun i=>(Φ i).dew.X) 1 i,Quiescent (Φ i) d (N.pow e i) ((Φ i).flag • x)→ Brush q b 1 (primaryP Φ d i) x) ((q:ℝ)^2) := by
    let q:=n+2; -- drop M
    let g:= N.pow e; obtain ⟨Z,hZ,H⟩:= (tithes (q:=q) p hk).cap; obtain ⟨a,ha,A⟩:= (reportD p hk hn hG hp hd).cap; obtain ⟨v,hv,K⟩:=(p.pocketSum hk hn hG hp hd).cap; obtain ⟨W,hW,hc⟩:= (p.log_sun hk hn hG hp hd he).cap; let f(i:ℕ):= ( (Z i+a i)+(v i+v i))+W i; let q':ℝ:= (q:ℝ)^2; have hh:1≤(q:ℝ):= Nat.one_le_cast.mpr (by unfold q; omega); have hl:1≤q':=one_le_pow₀ hh; have hr:= (hZ.blend (ha.mono hl)).blend ((hv.blend hv).mono (le_of_lt (zero_lt_one.trans_le hl))); intro q''; refine ⟨f,(hr.blend (hW.mono (by linarith))),?_⟩; filter_upwards [H,A,K,hc,p.f_current.pos,Pouch.small p.f_current Sienna.vow_ok] with i hi ha hk hc h hp;
    refine ⟨add_nonneg (add_nonneg (add_nonneg hi.1 ha.1) (add_nonneg hk.1 hk.1)) hc.1,fun x hx he=>?_⟩; let y:=(Φ i).flag • x; obtain ⟨hv,hf⟩:= hc.2 y he;
    have hy:= hi.2 y (he.near.trans_le hp) hv; let u' z:= Real.log ((Φ i).push z); let k:= Φ i; let p' z:=Real.log (k.dream (L' i z)); have hQ:1*1=(1:ℝ):=one_mul _;
    have hP: Brush q (Z i) 1 (fun z=> u' (L' i z)-u' y) x:= hQ ▸ Brush.reading (L' i) (show Brush q (Z i) 1 (fun z=>u' z-u' y) (L' i x) from hy) ((slopes h.le).trans hp); let p₁:=Real.log ∘ (V i); have hk': Brush q (v i) 1 p₁ x:=(hk.2 ⟨_,hx⟩).smaller (show q≤ n+3 from by unfold q; omega);
    let Q y:= primaryP Φ d i y; have hQ (z): Q z= u' (L' i z)-p' z- p₁ z:= by unfold Q primaryP capT; rw [inv_smul_smul₀ h.ne']; rfl
    refine (((hP.separating ((ha.2 x hx).smaller (show q≤ n+3 from by unfold q; omega))).separating (flash hk' (v i) hk.1 hk'.bound)).gathering ((Brush.certified zero_le_one _).climb hf le_rfl)).shimmy (Eventually.of_forall fun z=>?_); change Q z=(u' (L' i z)-u' (L' i x)-(p' z-p' x))-(p₁ z-p₁ x)+Q x; rw [hQ,hQ]; ring
-- At seam: full W.Corpus unreset. Unit normalized exponent.Composed with SETTLE at this step. Does not remove χ[constant].
def Vita (A:StagePort G U P X k L σ C M n)(x:A.dew.X):= Real.log (A.push x)-Real.log (A.push 0) + A.dew.β * A.bare (A.dew.grad, Model.Arbor.settle A.dew.c x)
-- x paid in UNSCALED. r=T.germ.Flag event.Radius reduced `n order budget` requires maturity. 
structure Loyalty (A:StagePort G U P X k L σ C M n)(r a d:ℝ)(x:A.dew.X) : Prop where
    quilt y : y∈ closedBall x r → Quiescent A d a y
    origin : Quiescent A d a 0
lemma iterationK (e:ℝ): ∃ s<0,∀ᶠ i in atTop, let φ := Φ i; let f:=MeterCoat Φ i; ∀ x:φ.dew.X,
     (∀ z∈ Metric.closedBall x (N.pow (-1) i), Quiescent φ d (N.pow s i) (f z))→ Brush (n+1) (N.pow e i) 1 (primaryP Φ d i) x:= by
    let z:=n+1; let τ:=((n+2:ℕ):ℝ); let T:=τ^2+1; obtain ⟨s,H⟩:= Lantern.iteration G L z (m:=e) (a:=1) (d:=T) zero_lt_one; let a:= min 0 s-1; have ha : a<s ∧ a<0:= by have hp:=min_le_left 0 s; have hx:= min_le_right 0 s; unfold a; constructor<;>linarith
    let U:= N.pow a; have hA:= (quouch p hk hn hG hp hd ha.2).meet (Eventually.of_forall fun i _ _ _ hx he x hp hk=> (he x hp hk).climb hx le_rfl) (show τ^2 < T from by linarith [show T=τ^2+1 from rfl]); have he:= (p.log_sun hk hn hG hp hd ha.2).meet (Eventually.of_forall fun i _ _ _ hx he x hp=> ⟨(he x hp).1, (he x hp).2.trans hx⟩) ha.1;
    refine ⟨a,ha.2,?_⟩; filter_upwards [p.plaza,hA,he,p.ferry.eventually H,p.f_current.pos] with i h ht hx hp hi φ K x h''
    have he z (hz:z∈ Metric.closedBall x (N.pow (-1) i)): z∈ P₀ i:= by
       have hv:= (h'' _ hz).near; apply mem_ball_zero_iff.mpr; apply lt_of_mul_lt_mul_left (a:= (tx) i) _ (show 0≤ tx i from hi.le); rw [mul_one,← norm_smul_of_nonneg (show 0≤ (tx i) from hi.le)]; exact hv
    let Yp:= primaryP Φ d i; have hf : N.pow (-1) i=betaF G (Φ i).pearlRide L ^ (-(1:ℝ)):=by rw [Meter.pow,h]
    rw [← h] at hp; apply hp ((Φ i).dew.X) ℝ Yp x; · intro x hP; exact ht x (he x hP) (h'' _ hP)
    intro x hx'; exact (hx (K x) (h'' x hx')).2
lemma wage (hr:Loom.Capture.race<τ)(he:τ <0)(hv:τ*((k:ℝ)+1)<e)(ht:e<0) (ha:e<a) : ∃ (s:ℝ),s<0∧ ∀ᶠ i in atTop,let φ:=Φ i; ∀ x:φ.dew.X, Loyalty φ (furl G L φ.pearlRide) (N.pow s i) d x→ 0<φ.push x∧ Brush (n+1) (N.pow a i) φ.flag⁻¹ (Vita φ) x:= by
   let e':=min (-1) e; obtain ⟨s,hs,h⟩:= iterationK p hk hn hG hp hd e'; let q:=min s (min e 0); have hq:q<0:= (min_le_left ..).trans_lt hs; let J i:= N.pow s i;
   -- need margin for term0 `capT(0)` accuracy Choice s<s₀`; strengthen Quiescent` monotone, use q=s−e′` fixed`. modify
   have heT:= (log_sun p hk hn hG hp hd hq); obtain ⟨f,hf,H⟩:=heT.cap; obtain ⟨u',hu,hU⟩:= (forever p hG hk hn hp (half_pos hd) hr he hv ht).cap;
   let F i:= (u' i+ N.pow e' i)+f i; have hF : N.Rush e F:= (hu.blend (Meter.Rush.any.mono (min_le_right ..))).blend (hf.mono ((min_le_right ..).trans (min_le_left ..)));
   obtain ⟨d',a,j,_,_,hT⟩:= p.ship; refine ⟨q,hq,?_⟩; filter_upwards [N.grows.eventually_ge_atTop 1,h,H,hU,p.f_current.pos,Pouch.small p.f_current Sienna.vow_ok,hT,p.plaza,(hF _ ha)] with i hi h heL hv hm hx hQ he H φ x hpQu; have hs:0<N.β i:= zero_lt_one.trans_le hi; let z:=N.pow (-1) i; have hz:0<z:=Real.rpow_pos_of_pos hs _; let op:= Φ i; let d₀:=furl G L φ.pearlRide; have hz':d₀=z:= congr_arg (· ^(-(1:ℝ))) he.symm;
   let K:= MeterCoat Φ i; let m':= (tx i)⁻¹ • x; have hX: K m'=x:= smul_inv_smul₀ hm.ne' _; have hk:= hpQu.quilt _ (mem_closedBall_self (show 0≤ d₀ from hz' ▸ hz.le)); let hq: ‖x‖<φ.flag:= hk.near
   have he : 0 ≤ (N.pow q i):= (Real.rpow_pos_of_pos hs _).le; let B (r:ℝ):= Quiescent φ d (N.pow r i); let I:=hQ.2.truePE;
   have hf:(F i)≥0:= add_nonneg (add_nonneg hv.1 (Real.rpow_nonneg hs.le _)) heL.1
   have hM : m'∈ P₀ i:= mem_ball_zero_iff.mpr (show ‖m'‖<1 from (by unfold m'; erw [norm_smul_of_nonneg (inv_pos.mpr hm).le]; exact (inv_mul_lt_iff₀ hm).2 (hq.trans_le (mul_one φ.flag |>.symm.le))))
   have hA:= h m' (fun y hh=>?_); swap;
   · let A:= closedBall m' z; have ht : K y∈ closedBall x d₀ := by
        rw [hz']; apply mem_closedBall_iff_norm.mpr; have h:‖y-m'‖ ≤ z:= mem_closedBall_iff_norm.mp hh; have hh: K y-x=φ.flag • (y-m') := by rw [smul_sub]; change _=_-K m'; rw [hX]; rfl
        rw [hh,norm_smul_of_nonneg hm.le]; exact (mul_le_of_le_one_left (norm_nonneg _) hx).trans h
     have hb:= hpQu.quilt (K y) ht; refine ⟨hb.near,hb.support,?_ ⟩; let Y' := relative φ.dew (windC φ d) (K y); let U':=(φ.dew).B.order G; let Φ':= ∫ x in Y', φ.notion (K y) x ∂U'; intro Yp F U; refine (show _ ≤ _*Φ' from hb.outside).trans ?_; apply mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hi (min_le_left ..)); exact MeasureTheory.integral_nonneg (StagePort.awake _)
   let V':= (V); let W (y):=Real.log (V i y);
   -- `F forever logS composition`, unfold relation by equality function
   let v y:= Vita φ (K y);
   let A:=capT Φ d i (0:φ.dew.X); let b (y:φ.dew.X):= W y-W 0- φ.dew.β * (φ.dew.℘ (K y)) + φ.dew.β * φ.bare (φ.smooth y)
   have hB: Brush (n+1) (u' i) 1 b m':= (hv.2 ⟨_,hM⟩).smaller (by omega)
   have H' : v=(b+ primaryP Φ d i-(fun _=> A)):= by -- sign verify: primary=logA−logDream−W. logDream=const−βJ, ⇒ Vita=b + primary(y)−A
      ext y; let Q z:= Real.log (φ.push z); let w z:=Real.log (φ.dream z); let Z:=φ.dew; have hp':φ.grader≠0:= by rintro h'; have h:= matter I hp 0; change 0<φ.grader*_ at h; rw [h'] at h; simp at h
      have hw (x): w x= Real.log φ.grader- Z.β*Z.℘ x:= by unfold w StagePort.dream; rw [Real.log_mul hp' (Real.exp_pos _).ne',Real.log_exp,neg_mul]; rfl
      change Q (K y)- Q 0+ Z.β * φ.bare (φ.smooth y)= b y+(Q (K y) -w (K y)-W _)-(Q 0-w 0-W _); rw [hw,hw, show Z.℘ 0=0 from cam_zero Z.B Z.T Z.label Z.L]; erw [show (φ.flag)⁻¹ • K y= y from (inv_smul_smul₀ hm.ne' y), smul_zero]; unfold b; change _= _ - _*Z.℘ (K y)+ Z.β*_+(_-(_-Z.β * Z.℘ (K y))-_)-_; ring -- adjust
   refine ⟨(heL.2 x hk).1,?_⟩; let L:φ.dew.X →L[ℝ] φ.dew.X:= morph (tx i)⁻¹; have hp : Brush (n+1) (F i) 1 v (L x):= by rw [H']; exact Brush.separating (hB.gathering hA) ((Brush.certified zero_le_one (x:=m') A).climb (heL.2 0 hpQu.origin).2 le_rfl)
   have hx:= Brush.reading («E»:= (Φ i).dew.X) L hp (slopes (inv_nonneg.mpr hm.le)); rw [one_mul] at hx; refine (hx.climb ((Real.norm_of_nonneg hf).symm.trans_le H) le_rfl).shimmy (Eventually.of_forall fun y=>?_); exact congr_arg _ (smul_inv_smul₀ hm.ne' y).symm -- syntax `E`
end Travel
end Provision
end YM.Contacts.Junction
