import YM.Contacts.Lintel.Origin
namespace YM.Contacts.Lintel
set_option linter.unusedSectionVars false
set_option quotPrecheck false
open Function Set Finset Filter Metric RG Wilson Lattice Precision Exterior MeasureTheory
open Bloch Milling Milling.Steam Pulse Spine MergeProof Milling.Forge Laurent Stationary Matrix Work.F05
open Milling.Garf Form House PertExtension.Series Tree Larch FreeResolvent PhysicalNext.RankCovariance
open PertExtension.Chart Radial
open scoped Topology BigOperators Matrix Classical NNReal ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {G:Gauge}{c f m: Side}{α:ℕ→Type}{n k:ℕ}
namespace Plata
open Crag Steam Lumen Resetter Ion Angle Convoy
namespace Sovereign
open Barrage Barrage.Reserve Rotor RG.Supply AnalyticNext.QuarticMatch.Sheets
variable (e: Oasis G) (x:G.ColorIndex)(E:∀ n,RackCore e.a e.M n) (K:Kin e.M e.Q) {s:RG.Supply.Sheet G} {U:Rolls s}{Q:PostCost U}{i j n m k:ℕ}
variable (hk:K.Planned Q)(ht: ∀ i n,i≤n → ∀ m,Bid.Sworn (e.M.H n i) m G) (hf: AsDivisors e.a.S)
local notation "V" => e.a.S
abbrev source (i n:ℕ):= K.path n i
abbrev level (e:Oasis G)(i:ℕ):= (e.a.params i).clip
abbrev Keystone (i n:ℕ):= ∀ m, Orbit (source e K i n) (hair (e.incident x E i n) m) (level e i)
include hk ht
lemma blazeDial {i n:ℕ} (m:Side)(hp:i≤n): Dial (e.M.H n i) (level e i) (source e K i n) m := by obtain h:= e.lamp.all n i hp m; exact ⟨⟨_,_,_,hk.cap n i hp⟩,ht i n hp m,hk.links n i hp, _,_,h⟩ -- noqa
omit ht
include hf
lemma home (n:ℕ): Keystone e x E K n n:= by
   rw [Keystone]; intro m; simp_rw [e.flares]; let F:=source e K n n; let P:=level e n; have hR:=hk.cap n n le_rfl; have hh : Precision.loop F (n:=m)=fun _=>0:=by funext x; unfold Precision.loop Patch.average Precision.uncut Atom.unmasked Atom.poly; simp only [show ∀ i, (F.loop i).coeff=0 from hk.initial n,Pi.zero_apply, zero_mul,sum_const_zero,tsum_zero,mul_zero]
   obtain ⟨k,hj,hL⟩:= hf m 0; let p:= (V).side n k; have hv:m.val∣p.val:= dvd_mul_of_dvd_left hL _;
   have hw (u: Link G m)(i:ℕ) (hi:i≤4): jet (intended P F) i u=jet (energy ∘ input G m) i u:= by
      let y : ℝ:= mult hv; let E(m:Side):= energy ∘ input G m; have hb:0<y:= mult_upper hv; apply mul_left_cancel₀ hb.ne'; rw [← jets_core hR hv];
      have hk:= hk.peak n k i hi; let L:= (arm G p 1).toContinuousLinearMap; let f(v:fieldDir G p 1):= mainTerm P F (represent v); let w(v:fieldDir G p 1):= Wilson.energy (represent v); let z:= still hv u;
      have ht: jet (intended P F) i z=jet (E p) i z:= by erw [show jet (intended P F) i z=jet f i (L z) from woven hk.1.analyticAt (arm G p 1).toContinuousLinearMap z i,show jet (E p) i z= _ from (show _=jet w i (L z) from woven hk.2.1.analyticAt (arm G p 1).toContinuousLinearMap z i)]; unfold jet; rw [show iteratedFDeriv ℝ i f 0=iteratedFDeriv ℝ i w 0 from hk.2.2];
      rw [ht]; -- straight private.S manually
      have hm(m:Side): AnalyticAt ℝ (E m) 0:= (starts _ Progress.Joint.energy_born.analyticAt (arm G m 1).toContinuousLinearMap);
      have h' : E p ∘ still hv=y • E m := funext fun x=> by unfold E Function.comp; rw [show input G p (still hv x)=copies hv (input G m x) from rfl,wilson_copy,nsmul_eq_mul]; rfl
      rw [←woven (hm p) (still hv) u i,h']; unfold jet; erw [iteratedFDeriv_const_smul_apply (hm m).contDiffAt]; change _*(y*_)= y*_; ring_nf; try rfl
   constructor
   · intro i hp H u; exact (hw u i H).trans (((fuel m 0 i u).trans (if_pos ⟨rfl,hp⟩)).symm)
   intro u; have he: turnSeries F.loop (m:=m)= fun _=>0:= funext fun i=> congr_fun hh _; change jet (turnSeries F.loop) 2 u=_; rw [he,Convoy.jet_empty]; exact ((Lumen.fuel m 2 2 u).trans (if_neg (by decide))).symm -- args
-- advanced
omit hf hk
private lemma whirl {j v:ℕ}{m:Side} (n:Side) (P:Patch)(Z:KernelChoices) (S:StepData n m)(he:S.patch=P)(hs:S.kernel=Z) (A:Spine.voyage P.L)(T:Spine.voyage S.patch.L) (h:HEq A T) (Q:ChartRatio G)(V':bore G) (F H:Bed)(F₀:Field (Fin v) (Node (Dye G))) {ζ:ℝ≥0}{a b:ℝ} (hv: let z:=Pulse.Spine.Origin.sprig P Z n; Two (voyageW n ζ _) F₀ (Forge.vault z Q (hair V' (n*P.L)) (installed z.ratio A) F.metric H.metric j v) a b) : Two (voyageW n ζ _) F₀ (Forge.vault S Q (hair V' m) (installed S.ratio T) F.metric H.metric j v) a b:= by
   have hR:m=n*P.L:= by have hM:=S.ratio.exact_size; change _=_*S.patch.L.val at hM; exact PNat.eq (he ▸ hM); -- ↑ conversion
   subst m; obtain ⟨P0,k0,s⟩:= S; change P0=P at he; change k0=Z at hs; subst P0 k0; have he:T=A:= (eq_of_heq h).symm; rw [he]; exact (show Two _ _ _ a b from hv) -- def proof irrelevance
local notation "M" => e.M
private abbrev per (e:Oasis G)(i p:ℕ):= e.a.S.side i p
private abbrev opS (e:Oasis G) (i p:ℕ):= e.a.clock.op i p
private def yields (i n p:ℕ):= let S:=opS e i p; Forge.vault S e.Q (hair (e.incident x E (i+1) n) (per e (i+1) p)) (installed S.ratio (e.vintage i n)) ((M).H n (i+1)).metric ((M).H n i).metric
lemma back_supports {i n:ℕ}(h:i<n)(j w:ℕ)(hw:w≠0) : ∃ (η:ℝ≥0) (b:ℝ),0<η∧∀ p:ℕ,Rooted (Range.cheap _) (yields e x E i n p j w-hair (e.entry x E i n) (per e i p) j w) (hush η (per e i p)*b):= by
   have ha:= seasons x e.oga e.lamp (E n) i h; obtain ⟨s,u,t,hs,he⟩:=ha.periodFunds; refine ⟨s,t j w,hs,fun p=> ?_⟩; let N:=per e i p; let X:= e.entry x E i n; let S:=opS e i p; have hf:= he N j w hw; let H:RackCore e.a e.M n:= E n;
   have hm':Two (voyageW N s _) (X j w) (yields e x E i n p j w) _ _:= whirl (F:=(M).H n (i+1)) (H:=(M).H n i) N (e.R i) _ S rfl rfl (e.vintage i n) (e.vintage i n) HEq.rfl _ (e.incident x E (i+1) n) (X j w) (ζ:=s) (a:=u j w) (b:=hush s N*t j w) (by
      intro z; unfold X; rw [e.fires x E i n h]; exact hf)
   letI: NeZero w:= ⟨hw⟩; obtain ⟨a,ha,hA⟩:=hm'.owes; have hv:a= _:=(show a=hair X N j w from focused ha (lower_onto _) (printFeeds hm'.risen)); exact hv ▸ hA
include hk ht
private abbrev candle (i n p:ℕ) := K.stationary n i p (planting (opS e i p).ratio (opS e i p).patch.odd_side)
private def Gm (i n p:ℕ):= thermal (S:=opS e i p) (planting (opS e i p).ratio (opS e i p).patch.odd_side) (art (opS e i p)) (level e (i+1)) (source e K (i+1) n) (candle e K i n p) e.Q
lemma makes_pure (i n p:ℕ) (h:i<n)(hg: Keystone e x E K (i+1) n)(hL:Bid.Larger (G:=G) (opS e i p)): Doric (yields e x E i n p) (intended (level e i) (source e K i n)) (Gm e K i n p ∘ arm G (per e i p) 1) := by -- typo
   let V':= e.incident x E (i+1) n; let W:= hair V' (per e (i+1) p); let P:= (M).H n i; let X:=(M).H n (i+1); let S:=opS e i p; let A:= candle e K i n p; let f:= (per e (i+1) p); let m:=(per e i p); let k:= e.J (i+1); have he:=hk.cap n _ h; let B:= planting S.ratio S.patch.odd_side; have hB:=hk.retains n i p h B; have hZ:=awakened e.lamp h; let fR:= installed S.ratio (e.vintage i n);
   let H:Spark.Beam S G fR X.metric P.metric (e.T.η k) := ⟨hL,hZ.edge,hZ.gap _, hZ.handy _,(e.lamp.crossings n i p h).trial⟩; have hv:=e.wild x E (i+1) n h;
   exact Plata.paid X P he H hZ.alive e.oga (hk.critical n i p h B).1 (hk.gap n i p h B) (Q.price _) ((hB.born (art S)).analyticAt) (hk.classicalPart n i p h B) (packaging (blazeDial e K hk ht f h) e.simple hv (hg f)) (hv.blazing.pri f) (blazeDial e K hk ht m (Nat.le_of_lt h))
include hf
lemma moonlit (i n:ℕ)(h:i<n) (he: Keystone e x E K (i+1) n) (m:Side): Doric (hair (e.entry x E i n) m) (intended (level e i) (source e K i n)) (paye m (K.alpha n i) (source e K i n) (level e i)):= by
    choose c hc hd using fun (k:ℕ)=> hf m k; let X(j:ℕ):= per e i (c j); let Φ(j:ℕ):= per e (i+1) (c j); have hp:Tendsto c atTop atTop:= tendsto_atTop_mono (f:=id) hc tendsto_id
    let δ:=e.J (i+1); let a:=Q.Γ δ; let z:=Q.c δ; have ha:0<a:=Q.pos _; have hb:0 < z:=Q.posC _; let W:= e.a.clock.loopCap (i+1); have hW : 0 ≤ W:= by have hf:0 ≤ e.a.clock.monitor (i+1):=(Real.exp_pos _).le; unfold W Calendar.loopCap; positivity
    obtain ⟨s,hs,T,hT⟩:= (e.forbes x E _ _ h).price; have hX : Tendsto (fun i=>(X i).val) atTop atTop:= (Extension.UV.Linear.side_diverges (V) i).comp hp; have h' : Tendsto (fun i=>(Φ i).val) atTop atTop:= (Extension.UV.Linear.side_diverges (V) (i+1)).comp hp
    let F k:= Sovereign.yields e x E i n (c k); have hy:= awakened e.lamp h; have hx:∀ᶠ j in atTop, Bid.Larger (G:=G) (opS e i (c j)):= ((hX.eventually_gt_atTop 1).and (h'.eventually_ge_atTop (100*Pressure.macroR (e.R i)))).mono fun j hj=> ⟨hy.alive,hj.2,hj.1⟩
    refine persistent (hk.cap n i h.le) (F:=F) (fun j=> (dvd_mul_of_dvd_left (hd j) ((V).denominator i).val)) hX hT (e.forbes x E _ _ h).honest.frame (W:=fun k=> Gm e K i n (c k)) (hx.mono fun j hx=> makes_pure e x E K hk ht _ _ _ h he hx) ?_ hb (mul_nonneg ha.le hW) (Eventually.of_forall fun j=>?_)
    · intro u v hv; obtain ⟨t,b,ht,H⟩:= back_supports e x E h u v hv; refine ⟨_, ?_, fun n=> H (c n)⟩; have hx : Tendsto (fun i=> hush t (X i)) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp (Real.tendsto_exp_atTop.comp ((tendsto_natCast_atTop_atTop (R:=ℝ)|>.comp hX).const_mul_atTop (NNReal.coe_pos.mpr ht))); simpa using! hx.mul_const b
    let t:=opS e i (c j); let S:= planting t.ratio t.patch.odd_side; have hy:= hk.retains n i (c j) h S; exact ⟨(hy.born (art t)).analyticAt,hy.classicalResult.analyticAt,fun p q u v hp hq=> (hy.wave_price (art t) p q u v hp hq).trans_eq (by unfold ports; unfold z a W δ Oasis.J; ring)⟩
lemma rejuvenated (h:i<n) (he: Keystone e x E K (i+1) n): salvia G x (e.entry x E i n 2 2)=K.alpha n i ∧ Keystone e x E K i n:= by
   obtain ⟨s,hs,T,hT⟩:= (e.forbes x E _ _ h).price; let H:=e.forbes x E _ _ h; let F:=e.incident x E i n; have ht₀:= e.lamp.all n i h.le; have hh: Platinum (e.entry x E i n) := caravan_even (e.wild x E (i+1) n h).grade _ ((M).H n i) e.Q; obtain ⟨hp,hs⟩:= congruous (hk.cap n i h.le) x hs hT (moonlit e x E K hk ht hf i n h he) H.honest (released e.lamp h.le) (ht₀ 1).starts (fun i=>(ht₀ i).symmetric.1) hh; exact ⟨hp, fun m=>by rw [show e.incident x E i n=_ from e.grub x E i n h]; exact hs m⟩ -- ht'
lemma largest (i n:ℕ)(h:i ≤ n): Keystone e x E K i n:= by induction h using Nat.decreasingInduction with| self=>apply home e x E K hk hf|of_succ i hi ih=> exact (rejuvenated e x E K hk ht hf hi ih).2
end Sovereign
open Sovereign Org Spec PhysicalNext.Repeat.Legato Milling Barrage.Reserve
lemma linked_arm (u:Passage G) (x:G.ColorIndex)(E:∀ n, RackCore u.A.B.a u.A.B.M n)(he:Mirage u.M.K u.A.B.a u.M.O)(h:G.Simple): let e:= coordinate u he h; let K:=u.A.B.kin; ∀ i n,i ≤ n→ Sovereign.Keystone e x E K i n ∧ (i<n→ salvia G x (e.entry x E i n 2 2)=K.alpha n i):= by
   let H:=u.A.B; let K:=H.kin; intro e K i n hn; let Q j m (he:j ≤ m)(n:Side):= show Bid.Sworn ((e.M.H m j)) n G from u.X.pledging.conducts.full m j n he; have hp X j (h:X≤j) := Sovereign.largest e x E u.A.B.kin u.A.B.support Q u.X.floor X j h; exact ⟨hp i n hn, fun h=> (Sovereign.rejuvenated e x E u.A.B.kin u.A.B.support Q u.X.floor h (hp _ _ h)).1⟩
end Plata
end
end YM.Contacts.Lintel
