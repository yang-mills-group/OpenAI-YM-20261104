import YM.X.Try.Siren
/-! # identity with non-H canonical computation. ∗Given witnesses Splot. Sparsity radius and tomography ∀some radius eventually small enough BOTH for background ℒ and exposures. B defined analytic solve∗. -/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Tri
open Lattice Wilson Maxwell Maxwell.Free MvPolynomial Function Set Filter MeasureTheory Asymptotics
open PertExtension LatticePT Next.Rank Next.Rank.Normal
open Pert Pert.Position Pert.RawLabels Pulse Bare Ribbon Detector
open Interval.Size Hinge Reed Stems Haze Interval
open Jet hiding Word
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{q:ℕ+}{F:Labels.Frames G}{d k m:ℕ} {V W I:Type*} {r R:ℝ}
variable (S:Bare.Shop F)(hq:1<q.val)(hg:G.Simple)(w:Floor R) (hr:R<r)
local notation "Fℕ"=>(atTop:Filter ℕ)
local notation "ℒ"=> Pert.Position.lower F 4 6
local notation "b₀" i=>S.bank q i 6 0
local notation "A₁"=> main q S
local notation "B"=> Bank F 6
local notation "Y"=> Splot.result F
local notation "γ"=> YM.PositionX.par F 6
local notation "ℝ₀"=> Pulse.Region
local notation "L"=> Pulse.away
local notation "b·" => pureBank F 6
variable {x:Pert.Position.E F 6} (hx:YM.PositionX.par F 6 x= -x)(s:Splot F)
def sterile (s:Splot F) := Y s (pureBank F 6)=0
include hx hq hg hr
variable (v:Fin m→ Splot F)(h:LinearMap.ker (LinearMap.pi (fun i=> Splot.result F (v i) (pureBank F 6) ∘ₗ (halfling F).subtype))=⊥) (hw:∀i,width (v i) r)
include hw h
lemma driftR : Released (fun i=> positive F (σ (q:=q) S w i x)):= by
    let X(i:ℕ):= LinearMap.pi (fun j:Fin m=> Y (v j) (b₀ i) ∘ₗ (halfling F).subtype); refine Op.grip (X:=X) ?_ h (Released.piR (fun j:Fin m=> remit_tip S hq hg w hr x hx (v j) (hw _))); intro p; apply tendsto_pi_nhds.mpr; intro j; exact S.bank_white q hq (s:=Splot.sit F p.val (v j)) -- name
set_option maxRecDepth 5300 in
lemma no_drift (hs:sterile s) : Tendsto (fun i=>lookie F (s.sit F x) (remit q S (fun i=>Pulse.away (q:=q) (k:=i) S w 6) i) - lookie F (s.sit F x) (A₁ i 6 w 1)) Fℕ (𝓝 0):= by
   let M(i:ℕ):= bufferL F (barter (q:=q) (k:=i) (d:=6) S w); let u(i:ℕ):= Pulse.away (q:=q) (k:=i) S w 6; obtain ⟨c,hc⟩:= driftR S hq hg w hr hx v h hw; let z(i:ℕ):= positive F (σ (q:=q) S w i x)
   have he : Tendsto (fun i=> Y s (b₀ i) (z i).val) Fℕ (𝓝 (Y s (pureBank F 6) c.val)) := Op.touch (lamp S hq s) (show Tendsto (fun i=> (z i).val) Fℕ (𝓝 c.val) from continuous_subtype_val.continuousAt.tendsto.comp hc)
   unfold sterile at hs; rw [hs,LinearMap.zero_apply] at he; apply he.congr; intro i
   have hX: Y s (A₁ i 6 w 1) x= Y s (remit q S M i) x:= by
       let A:= A₁ i 6 w; let P:= s.sit F x; let f:= S.bank q i 6; let b:= (barter (q:=q) (k:=i) (d:=6) S w)
       have he: bufferL F (-b)=- M i:= LinearMap.ext fun _=>rfl
       change predMarket _ f 1 s.n s.test P.p=_; rw [come_zero _ _ _ _ (tender_zero ..),tender_one,he];
       change f 1 s.n s.test _ + _= f 1 s.n s.test _- passV (M i) (f 0 s.n s.test) P.p; simp only [pass_view,LinearMap.neg_apply,MultilinearMap.map_update_neg,Finset.sum_neg_distrib, sub_eq_add_neg]; rfl
   change _=Y s (remit q S u i) x-Y s (A₁ i 6 w 1) x; rw [hX]; rw [← s.accepts F hg (weatherless ..)];
   have he (b c:B): Y s (b-c) x=Y s b x-Y s c x:= rfl
   unfold remit; simp_rw [he,σ,LinearMap.sub_apply,map_sub]; rw [s.pass_S F hg (weatherless ..) hx _ (fun v hv=> (shield (q:=q) S w v hv i).2), s.pass_S F hg (weatherless ..) hx _ (fun v hv=> (shield (q:=q) S w v hv i).1)]; ring
omit h hw
local notation "D"=> nested F hg S 6
variable (hR:∀ i:(nested F hg S 6).rail.reached, Curve ((nested F hg S 6).rail.reachedV i).f ⊆ Pulse.Region ((nested F hg S 6).rail.reachedV i).r r)
-- chart calc lemma. zero frame part
omit hq hr
include S
lemma chart_zero (p:Buffer F 6)(H:sterile s): fderiv ℝ (YM.PositionX.cross F (s.sit F x).p) (expose F s.test (pureBank F 6),0) (0,p)=0:= by
   let f:= YM.PositionX.cross F (s.sit F x).p; let z:= (expose F s.test (pureBank F 6),(0:Buffer F 6)); let t(a:ℝ):= (z.1,a • p)
   have ht: HasDerivAt t (0,p) 0:= by convert! ((hasDerivAt_const (0:ℝ) z.1).prodMk ((hasDerivAt_id' (0:ℝ)).smul_const p)) using 1; simp
   let A:= (s.sit F x); change fderiv ℝ f z (0,p)=0; apply ((cross_smooth F A.p).differentiable (by simp) z).hasFDerivAt.comp_hasDerivAt_of_eq 0 ht (by simp [z,t]) |>.unique; change HasDerivAt (fun a:ℝ=> YM.PositionX.cross F A.p (expose F A.f (pureBank F 6), (a • p:Buffer F 6))) (0:ℂ) (0:ℝ); simp_rw [cross_market];
   apply HasDerivAt.congr_deriv (income A.f A.p (pureBank F 6) p); change Splot.result F s (billM F (bufferL F p) (pureBank F 6)) x=0; unfold sterile at H; rw [s.pass_S F hg (p:=x) (by apply S.all_par) hx _ (fun a h=> p.property.2.1 _ (by omega) _ h), H, LinearMap.zero_apply] -- name
-- D shift through exposure
include hq hr hR
lemma fade (H:sterile s)(h':width s r): Tendsto (fun i=> Y s (A₁ i 6 w 1) x-Y s (S.uncut hg q i 6 1) x) Fℕ (𝓝 0):= by
   let p:= s.sit F x; let B₁ (i:ℕ) := A₁ i 6 w; let b:=fun i=> (D).report (B₁ i); let f:= YM.PositionX.cross F p.p; let E:= expose (d:=6) F p.f; let N:= Lens F 6 p.r; let z:= (E (pureBank F 6),(0:Buffer F 6)); let L₁:=fderiv ℝ f; have hv:=fun (s: Pert.Position.Section F 6)=> steady_b S hq w s
   obtain ⟨l,hl⟩:= lens_ready (u:=p) S hq hg w hr h'; obtain ⟨g,hg'⟩ := page_leaves D B₁ hv (by choose x hx using (fun i:(D).rail.reached=> lens_ready (u:=(D).rail.reachedV i) S hq hg w hr (hR i)); exact ⟨x,tendsto_pi_nhds.mpr hx⟩) -- unresolved N let.
   have he : Continuous (fun a: (N×Buffer F 6) × (N×Buffer F 6)=> (L₁ a.1) a.2):= (((cross_smooth F p.p).continuous_fderiv (by simp)).comp continuous_fst).clm_apply continuous_snd; let A(i k:ℕ):=E (B₁ i k);
   have hz : Tendsto (fun i=> A i 0) atTop (𝓝 z.1):= expose_leg F hv _
   have hL:= he.continuousAt.tendsto.comp ((hz.prodMk_nhds (page_sticks D B₁ hv)).prodMk_nhds (hl.prodMk_nhds hg')); have hK:= he.continuousAt.tendsto.comp ((hz.prodMk_nhds (tendsto_const_nhds (x:=(0:Buffer F 6)))).prodMk_nhds (hl.prodMk_nhds (tendsto_const_nhds (x:=(0:Buffer F 6)))))
   have ht:= hK.sub hL; change Tendsto (fun i=> L₁ (A i 0,0) (A i 1,0)- L₁ (A i 0,b i 0) (A i 1,b i 1)) _ (𝓝 (L₁ z (l,0)-L₁ z (l,g))) at ht; rw [show (l,g)=(l,(0:Buffer F 6))+(0,g) from by simp,map_add, show L₁ z (0,g)=0 from chart_zero S hg hx s g H, add_zero,sub_self] at ht
   refine ht.congr' ?_; filter_upwards [(D).patches (q:=fun i=> S.bank q i 6 0) (S.bank_white q hq)] with i hi
   have hk(q:Jet.Word (Buffer F 6)): Y s (predMarket q (B₁ i) 1) x= L₁ (A i 0,q 0) (A i 1,q 1):= by change lookie F p _=_; rw [all_tips (w:=B₁ i) (b:=q) (s:=p),flow_tip _ _ ((cross_smooth F p.p).differentiable (by simp) _)]; rfl
   have hp:Y s (B₁ i 1) x= Y s (predMarket 0 (B₁ i) 1) x:= by change B₁ i 1 p.r p.f p.p= predMarket 0 (B₁ i) 1 p.r p.f p.p; rw [come_zero (B₁ i) (0:Jet.Word (Buffer F 6)) p.f p.p rfl]; simp [pass_view, bufferL_eq] -- name order
   have hh:S.uncut hg q i 6=predMarket (b i) (B₁ i):= coincideH D (p:=tender q S i 6 w) _ (tender_zero ..) hi; change _=Y s (B₁ i 1) x - _; rw [hp,hh,hk,hk];rfl
end YM.PositionX.Tri
