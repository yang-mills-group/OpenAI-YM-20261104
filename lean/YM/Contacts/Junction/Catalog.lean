import YM.Contacts.Junction.Opus
/-! # aperture choreography witness. Multiple-contact comparisons need these at auxiliary periods unperturbed. -/
noncomputable section
namespace YM.Contacts.Junction
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Function Filter Set Finset Metric Lattice RG Gauge Pressure Wilson PertExtension.Series MeasureTheory
open Radial Precision Matrix PhysicalNext.Repeat Bid Tree Tested PertExtension.Chart Lapis Milling
open YM.Stationary Milling.Forge Exterior Push.Uniform ConnectedActivityE6 Blaze Shield Poll Next.SectorChange Fare Model.Arbor
open scoped Topology ContDiff Pointwise BigOperators Matrix.Norms.Frobenius Classical NNReal
variable {G:Gauge} {P : ChartRatio G} {σ C e v d t K τ ω':ℝ}{n k j r i:ℕ}
namespace Provision
open Ion House Lintel Lintel.Angle Cove Model Province.Costing Lumen Pulse Spine Steam
open Milling.Garf Loom Loom.Patch Meter Capture Buyer Push Current Milling.Spark
open Sienna Lantern Planned.JetPort Dew Uniform
open Push.AbsoluteSums -- name???
structure StagePort (G:Gauge) (κ:Teller G) (P : ChartRatio G) (x : G.ColorIndex) (k:ℕ) (L:Side) (σ C:ℝ)(M:Uniform.ChartPrices)(n:ℕ) where -- data
    dew : Dew G
    budget : BudgetPoint
    importB : bore G
    hBed : Bed
    outB : House (Lines G dew.c 1)
    pearlRide : ℝ -- actual t hat-coarse
    taxi : ℝ -- dim-cost Bolt
namespace StagePort
variable {U:Teller G} {L:Side} {M:Uniform.ChartPrices}{X:G.ColorIndex}
structure Up (i:StagePort G U P X k L σ C M n)(d a:ℝ)(j:ℕ): Prop where
    truePE : let D:= i.dew; Pearl U i.taxi i.pearlRide L σ C M n i.budget D
    lit : let D:=i.dew; ∀ x≤ k,Charted G k (betaF G i.pearlRide L) i.budget D.T.up i.importB D.T.high d (ripe (betaF G i.pearlRide L)) a x j
    bankW : Aegis X i.importB i.hBed
    vast : 10*i.budget.B < i.dew.f.val
    port : let D:=i.dew; let F:=hair i.importB D.f; Package (material D.T.high D.T.up) F 5 ∧ Package (hand F (k+3)) F (k+3) ∧ ∃ b, Sight (runner (visitor D.S (hand F (k+3))) D.B) (swell i.outB (k+3)) b k
variable (v:StagePort G U P X k L σ C M n)
local notation "W" => v.dew
abbrev root_ν := Dew.fan P W
abbrev bench := scoreP P v.dew.B v.dew.T v.dew.label v.dew.L (trib k v.budget v.importB v.dew.T.high v.dew.T.up)
abbrev natal := scoreP P v.dew.B v.dew.T v.dew.label v.dew.L (biomass k v.budget v.importB v.dew.T.high v.dew.T.up)
def eternal :=classic P v.dew.B v.dew.T v.dew.label v.dew.L (hand (hair v.importB v.dew.f) (k+3))
abbrev targetY:= swell v.outB (k+3)
abbrev bare := Radar.gap v.targetY
abbrev μ:= Poll.sweep v.dew.matrix⁻¹
abbrev flag := eaves G L v.pearlRide
abbrev crab (x:v.dew.X)(y:v.dew.Y): v.dew.Q:=((v.dew.grad, v.flag • x), v.dew.grad • y)
abbrev smooth (x:v.dew.X): cap G v.dew.c:= (v.dew.grad, Model.Arbor.settle v.dew.c (v.flag • x))
end StagePort
open StagePort
variable {U:Teller G} {L:Side} {M:Uniform.ChartPrices}{X:G.ColorIndex} {Φ:ℕ→StagePort G U P X k L σ C M n}
local notation "ι" => StagePort.dew ∘ Φ
local notation "E" => Dew.X ∘ (ι)
local notation "Y" => Dew.Y ∘ (ι)
local notation "Xr" => fun i=> Dew.Q (ι i)
variable {N:Meter}{Q:ℝ→ℝ}
structure Travel (N:Meter)(Q:ℝ→ℝ)(Φ:ℕ→StagePort G U P X k L σ C M n):Prop where
   shape : Bolt G L Q
   frames : ∀ᶠ i in atTop, (Φ i).taxi = Q (Φ i).pearlRide
   ferry : Tendsto (fun i=>(Φ i).pearlRide) atTop atTop
   plaza : N.β =ᶠ[atTop] fun i=> betaF G (Φ i).pearlRide L
   ship : ∃ d a:ℕ→ℝ,∃ j:ℕ→ℕ,(∀ e,N.Rush e (fun i=> N.pow (-d i) i))∧ N.Rush 0 (fun i=> N.pow (a i) i) ∧ ∀ᶠ i in atTop,n+3≤ j i∧ StagePort.Up (Φ i) (d i) (a i) (j i)
   funds : Spectrum N k (S:=fun i=>(Φ i).outB) 0
local notation "Zr" => (Frame.Port (Y) (N.pow stashp))
namespace Travel
variable (p:Travel N Q Φ)(hk:2≤k)(hG:G.Simple)(hp:LocalRatio P)
include p
lemma scale : N.Rush 0 fun i=> (Φ i).taxi:= (Meter.Rush.grounded p.shape.uses p.ferry p.plaza).take p.frames
lemma dawn : ∀ᶠ i in atTop, Pearl U (Φ i).taxi (Φ i).pearlRide L σ C M n (Φ i).budget (Φ i).dew:= by obtain ⟨d,a,j,_,_,H⟩:=p.ship; exact H.mono fun i hi=> hi.2.truePE
variable (hp':0<d)
include hp'
-- μ appointments.
lemma heat : Patch.Shell N (fun i=>(Φ i).μ) (fun i=>wick G L d (Φ i).pearlRide) := by
   have hf := wordPos p.dawn p.scale
   let C:= (M.gap/2)⁻¹; have ht: 0<C:= inv_pos.mpr (half_pos hf.1); refine Patch.distant (C:=C) (W:=fun i=>(Φ i).dew.matrix⁻¹) ?_ G L Q p.ferry p.plaza ?_ p.shape ht hp';
   · filter_upwards [p.dawn] with i hi; let D:=(Φ i).dew; obtain ⟨A,hA,hM⟩:=hi.service; have hv:=Lapis.wakes D.B D.label D.T.up D.T.high D.ρ _ _ _ A hi.stitches.large hi.staples hA (x:=0) (by rw [norm_zero];exact hA.x_pos); exact ⟨hv.1.inv,fun x=> le_trans (hv.2.2.1 x) (by rw [hM])⟩
   · filter_upwards [p.dawn,p.frames] with i hi hx; exact (Lapis.countsK (G:=G) (Φ i).dew.B (Φ i).taxi hi.stitches.overall).trans_eq hx
lemma quarry : N.Rush 0 (fun i=>wick G L d (Φ i).pearlRide):= Meter.Rush.grounded (Sienna.gen G L d) p.ferry p.plaza
omit hp'
lemma f_current : Pouch N vow (fun i=>(Φ i).flag):= by
   let H i:=(Φ i).flag; have he : N.pow vow=ᶠ[atTop] H:= p.plaza.mono fun i hi=> congr_arg (fun x=> x^ (vow:ℝ)) hi; refine ⟨((N.eventual).and he).mono fun i hi=> (show 0<H i from lt_of_lt_of_eq (Real.rpow_pos_of_pos hi.1 _) hi.2), (Meter.Rush.any (p:=vow)).take he.symm, Pouch.canon.back.take ((he.symm).mono fun i hi=> congr_arg (fun x:ℝ=>x⁻¹) hi)⟩
local notation "γ" => (γC (ι))
lemma parameter : Pouch N (-(1/2)) γ:= (volume_count p.dawn p.scale p.plaza p.ferry).2.2
lemma fC : N.Rush fit γ∧ N.Rush fit (fun i=>(Φ i).flag):= ⟨p.parameter.forward.mono (by norm_num [fit]),p.f_current.forward.mono (by norm_num [vow,fit])⟩
variable (hn:k≤ n)
local notation "ν" => (Frame.Port (fun i=> Dew.Q (ι i)) (N.pow stashp))
include hG hp hk hn
set_option maxHeartbeats 400000 in
lemma presentFee : Root N (fun i=>(Φ i).bench) (n+3) 0 (N.pow stashp) ∧ Root N (fun i=>(Φ i).natal) (n+3) 0 (N.pow stashp) ∧ (∀ e:ℝ, Budget N ν (n+3) e (fun i _=> (Φ i).bench-(Φ i).natal)) := by
   obtain ⟨d,a,j,hD,ha,H⟩:=p.ship; let V(i:ℕ):= (Φ i).dew; let B(i:ℕ):=(Φ i).budget; let Yy i:=(Φ i).importB; let M i:= shuttle (V i).B (V i).L; have hW:= winds (k:=n+3) p.dawn p.scale;
   let g(i:ℕ):= biomass k (B i) (Yy i) (V i).T.high (V i).T.up (f:=(V i).f);
   let ℓ i := boom k (B i) (Yy i) (V i).T.high (V i).T.up (f:=(V i).f)
   have hy : N.Rush 0 (fun i=> (Fintype.card (Site (V i).f):ℝ)):= Rush.bb p.scale (p.dawn.mono fun i hi=>⟨Nat.cast_nonneg _,hi.stitches.finalP⟩)
   have ht: ∀ᶠ i in atTop,(V i).T.up.Bounds (V i).T.high σ C (loopBill G L (Φ i).pearlRide):= p.dawn.mono fun i hi=>hi.staples
   have hX : ∀ᶠ i in atTop,∀ q≤ k,Charted G k (N.β i) (B i) (V i).T.up (Yy i) (V i).T.high (d i) (ripe (N.β i)) (a i) q (j i):= by filter_upwards [H,p.plaza] with i hi hv; rw [hv]; exact hi.2.lit
   have hℓ t: Budget N ν (n+3) t (fun i _=>ℓ i ∘ M i):= gleaming ht hX (H.mono (fun i hi=>hi.2.bankW)) hG (hh:=H.mono fun i hi=> hi.2.vast) hy hD hk hW t -- namespace Current.G args may
   have hg : Budget N ν (n+3) 0 (fun i _=> g i ∘ M i):= whirs hX hy ha hW (H.mono fun _ hi=>hi.1) ((smallLan p.dawn p.scale).mono (fun i hi k=> hi k.val k.property)); let q i:= (Φ i).bench; let ℘ i:= (Φ i).natal; have hh := clearFan P p.dawn p.scale p.plaza p.ferry hp (hk:=le_rfl)
   let Ee(i:ℕ): Type:= (V i).Q; let f:∀ i,Ee i→ℝ:= fun i=> ℓ i ∘ M i; have ht:∀ i,(Φ i).bench= ℘ i+f i:= fun i=>funext fun x=> (add_assoc ((V i).fan P x) (g i (M i x)) _).symm
   have hΩ:= Arms.sum hh.price hg; change Budget N ν (n+3) 0 (fun i _=> ℘ i) at hΩ; have he (i:ℕ)(he:∀ q'≤ k,Charted G k (N.β i) (B i) (V i).T.up (Yy i) (V i).T.high (d i) (ripe (N.β i)) (a i) q' (j i))(hu:AnalyticAt ℝ ((V i).fan P) 0) : AnalyticAt ℝ (q i) 0∧ AnalyticAt ℝ (℘ i) 0:= by
       have hh :AnalyticAt ℝ (g i ∘ M i) 0:= AnalyticAt.comp (x:=0) (f:=M i) (g:=g i) (by unfold M; rw [shuttle0]; exact loomT he) (shuttleH ..); have hv :AnalyticAt ℝ (f i) 0:= AnalyticAt.comp (x:=0) (f:=M i) (g:=ℓ i) (by unfold M; rw [shuttle0];exact (tribX he).1) (shuttleH ..); exact ⟨(show q i=℘ i+f i from ht i) ▸ ((hu.add hh : AnalyticAt ℝ (℘ i) 0).add hv),hu.add hh⟩
   have hR := hh.analytic; refine ⟨⟨(Arms.sum hΩ (hℓ 0)).confirm (Eventually.of_forall fun i => ?_), (hX.and hR).mono fun i hi=> (he i hi.1 hi.2).1⟩, ⟨hΩ,(hX.and hR).mono fun i hi=> (he i hi.1 hi.2).2⟩, fun t=>?_⟩; · exact funext fun _=> ht i
   exact Arms.confirm (Eventually.of_forall fun i:ℕ=> funext (fun j=> show q i-℘ i=f i from (by unfold q; rw [ht]; abel))) (hℓ t)
lemma flowFee : ∀ᶠ i in atTop, Measurable (Φ i).bench ∧ Radial.Stationary (Φ i).bench ∧ ∀ x,skel (Φ i).bench 3 x=(Φ i).dew.℘ x.1.2 + Junction.gram (Dew.B (ι i)) (Dew.matrix (ι i)) x.2 := by
   obtain ⟨d,a,j,-,-,H⟩:=p.ship; filter_upwards [H] with i hi; let A:=Φ i; let D:= A.dew; let v:=D.label; let Yy:=hair A.importB D.f; let t:=trib k A.budget A.importB D.T.high D.T.up (f:=D.f); let f:= A.bench; obtain ⟨hZ,he,c,hq⟩:=hi.2.port; have h:=hi.2.truePE; have H:=hi.2.lit; obtain ⟨B,hB,hb⟩:= h.service
   have hs:= Buyer.hands h.staples H hk hG hi.2.bankW he hZ; have hy :AnalyticAt ℝ t 0:= (loomT H).add ((tribX H).1); obtain ⟨ha,h'⟩:= Cove.enamel P D.B D.T v D.L h.staples h.stitches.large hp hy hs.1; let V := table D.B v D.T.up D.T.high; have hK:= kernelCost D.B D.T v h.staples h.stitches.large
   have hw : Radial.Stationary f:= ⟨ha.contDiffAt,(jet_zero f 0).symm.trans ((h' 0 0 (by decide)).trans ((jet_zero ..).trans hK.2.base0)),fun i=> ((h' i 1 (by decide))).trans (hK.2.base1 _)⟩
   have hm : Continuous (shuttle D.B D.L):= (clockF (G:=G) D.B).continuous.prodMk ((laneH _).comp D.ℓ.continuous); refine ⟨(ribbon_caps P D.B D.T v _ h.staples h.stitches.large hp).add (g:=t∘ shuttle D.B D.L) ((tribX H).2.2.comp hm.measurable),hw,fun z=> ?_⟩
   have h_: jet f 2 z=jet (V ∘ levelL D.L) 2 (z.1.2,z.2):= by rw [show jet f _ _= _ from h' z 2 le_rfl, Milling.Garf.woven (F:=V) hK.1]; rfl
   unfold skel; change ∑ i∈Finset.range 3,jet f i z= _; rw [Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_range_succ]; erw [jet_zero,hw.base0, hw.base1,h_]; rw [sum_range_zero]; simp only [add_zero,zero_add]; exact cleavage D.B D.T v hB h.staples h.stitches.large z.1.2 z.2
end Travel
end Provision
end YM.Contacts.Junction
