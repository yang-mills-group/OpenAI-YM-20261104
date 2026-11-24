import YM.RG12.Rail.Run
import YM.RG12.Joint.Stack
import YM.RG12.Common.Concourse
import YM.RG12.Joint.Silk
import YM.OPE.ElementaryLog
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.RG12Joint
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Bandage
open InteractingRank Next.Rank Next.Rank.Tapes RankCovariance PhysicalNext.InteractingRank.Soft
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} (hG : G.Simple)
/-!
# Joint variant of the UV-Refinement proof. Pays both copy quotas.

Scheduling argument adapted from uv_havens/uv_wishes and noel_planned, both in this seed.
Use just one uv_footed theorem, retaining the receipts still needed after it. Don't align two
outputs of existence type. -/
open Next.Extract Dash
open YM.MergeProof MergeProof.Accent MergeProof.East
open UVExtension UVExtension.Harvest
open YM.Pert.Dense YM.RG12.Commission
include hG
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1400000 in
theorem lit_construct {b:ℝ}(h:0<b): ∃ C:Family G, C.path.levels.clock.kernel.penalty=b ∧ Spec.Calibrated C ∧ C.Makes ∧ Extraction.Wcmain C ∧
    UVExtension.Oasis.Floral (hG:=hG) C ∧ (∃ (A:YM.RG12.Commission.Port C) (hC:C.Makes), ∃ lit:ℕ→Prop,YM.RG12.Rail.Outbound A lit hC) ∧ (∃ W r D, OPE.Log.LogPackage C W r D) ∧ Acme.Aroma C ∧ (∀ F:Extraction.Order, Cells.CellHyp C F → Grill C F∧MergeProof.East.CompleteWeak C F)∧∀ f:Extraction.Order, ∃ (g:Extraction.Order) (A:Table C.book) (L:ℕ→Table C.book) (R:Bin A) (T:Table C.book) (E:DiffPlan T), Next.Extract.Base C (f.refine g) A L R T E ∧ ∃ s:Spec.Seed C (f.refine g) T,Maxwell.Ranks T s.kernel.spin:=by
  obtain ⟨kG,hb,hkern⟩:= YM.Axial.viable G b h
  let v: Orders:= ⟨4,fun i=>6+i,fun i=>2+i,fun i=>100⟩
  have hE (i:ℕ): 100 ≤ v.supportExp i:= by exact le_rfl
  have hp : Draft v:= by
    refine ⟨le_rfl,fun i j hij=> Nat.add_le_add_left hij 6,fun i j hij=> Nat.add_le_add_left hij 2,fun i j hij=>?_,fun i=> lt_of_lt_of_le (by norm_num) (hE i),fun i=>by change _ ≤6+i; omega,fun i=>by change _≤2+i; omega⟩
    exact le_rfl
  let Q(i:ℕ):=i+1; have hQ: Monotone Q:=fun i j hj=>Nat.add_le_add_right hj _; have hQ'(i):1≤ Q i:=Nat.le_add_left ..
  let Q1:ℕ→ℕ:=fun _=>1

  obtain ⟨V,W,hV⟩:= Push.Mark.commissioned G (hol G) (Labels.frames G)
  obtain ⟨s,T,C,K',hP,hv,hC⟩ := uv_footed hG hkern v hp Q
  let u:Tariffs:=⟨fun _=>0,fun _=>le_rfl,fun _=>1⟩
  let X:Extra.Multi.Scope:=⟨fun _=>1,fun _=>0,fun _=>1,fun _=>le_rfl,fun _=>Nat.zero_lt_one⟩
  obtain ⟨t,hT,hx⟩:= hC u X; obtain ⟨Kc,L,hL⟩:= oyster s W V hV
  have ho:Tendsto (fun i=>(s.profile i).order) atTop atTop:= tendsto_atTop_mono (f:=id) (g:=_) (fun i=> by rw [hv.jets]; exact (le_max_right ..).trans (hp.k i)) tendsto_id
  obtain ⟨z,p,μ,-,-,hμ,hf⟩:= capitalSnow s (UVExtension.Case.actualPay s T) ho
  obtain ⟨O⟩:= Next.Rank.exists_budget G
  obtain ⟨uC,hU⟩:= bulletin s (UVExtension.Case.actualPay s T) ho
  obtain ⟨B0,hBoard⟩:= Mast.RG12Joint.extra_board s T
  let k:= (((t⊔L)⊔ μ)⊔ uC) ⊔ B0
  have heK: t ≤ k ∧ L ≤ k∧ μ≤k∧uC≤k∧ B0≤k:=by have h:(((t⊔L)⊔ μ)⊔ uC) ⊔ B0≤k:= le_rfl; simp only [sup_le_iff] at h; exact ⟨h.1.1.1.1,h.1.1.1.2,h.1.1.2,h.1.2,h.2⟩
  obtain ⟨hK,hl,hB0,hUC,hBC⟩:= heK
  let M:= UVExtension.Case.provider s T k; obtain ⟨⟨P⟩,hk⟩:=hx k hK; change Rolls M.p at P
  have hRe : Relay M.p M.K uC:=by
    obtain ⟨b,F,ψ,he,v⟩:= hU.bulletin
    refine ⟨b,F,ψ,he,v.same,?_,?_,?_⟩
    · intro i; refine ⟨(v.buys i).1,(v.buys i).2⟩
    · intro i; exact ⟨(v.shops i).1⟩
    intro i d j;exact v.lifts i d j

  have hz : RelayP M.p M.K uC:=by
    obtain ⟨b,F,ψ,he,v⟩:= hRe.bulletin
    exact ⟨b,F,ψ,fun i=> (he i).frequently,v⟩
  let Ht (i j:ℕ): JointLoad.Clockwork.Menu:= ⟨Push.SectorMeasure.Chi.canonical,1,0,0,0,0,0,0,one_pos,le_rfl⟩
  let J (i j:ℕ):JointLoad.Folio.Aux:=⟨40,1,1,le_rfl⟩
  let E(i j:ℕ) : Next.Scheduling.Exchange:=⟨0,0,1,1,1,0,0,by norm_num⟩
  obtain ⟨w,H⟩:= hk P
  let Qt(i j:ℕ):Postage:=⟨1,1,1,1,le_rfl,zero_lt_one,zero_lt_one⟩
  let xi:Extra.Multi.Tariff:= ⟨1,0,fun _=>le_rfl⟩
  obtain ⟨F,hF⟩:= H w le_rfl Qt E xi
  obtain ⟨θ,-,hH⟩:= hF _ (fun _=>one_pos)
  let V': Delays θ:=⟨fun _=>0,fun _ _=>0,fun _=>1,fun _=>1⟩
  obtain ⟨V₀, -, hu'⟩ := OPE.halo_delay V'; obtain ⟨W₀,hw0,hw'⟩:= OPE.Log.aux_delay V₀; obtain ⟨Wb,hWb,hFb⟩:= silk_extra W₀
  let S:Delays θ:= {Wb with shells:= fun i => max (Wb.shells i) (snows P i)}; have hs:DelayLe Wb S:= ⟨le_rfl,le_rfl,fun _=>le_max_left ..,le_rfl⟩
  obtain ⟨a,hα,hδ⟩:= shower Kc S
  obtain ⟨V_s,hSl,hSLe⟩:=YM.RG12.Rail.fits (P:=P) a
  obtain ⟨l,h₁S,h₂⟩:= hiss Q V_s; let h₁:= hSl.trans h₁S; obtain ⟨l',hₐ,h₂'⟩:= hiss Q1 l; obtain ⟨q,hφ,hM,h₃⟩:= hH Ht J l'
  have hwS:= hα.trans (h₁.trans (hₐ.trans hφ)); have hwB:=hs.trans hwS
  obtain ⟨D,-⟩:= Bar.exists_above q 2; let I:Wait D:= ⟨fun _=>0,fun _ _=>0,fun _=>by simp,0⟩
  have hG'(i):0≤ generator G i := by unfold generator; positivity
  obtain ⟨Q',Z₀,hZ,h₄⟩:= franchise M.K O (generator G) hG' hG (hf k).1 (hf k).2 (fun i=> (hB0 i).trans (P.large i).need) hμ I
  obtain ⟨Z1,hzd,hzL,hzK,hZ'⟩:= sponsored hG M.K O (Next.Foundations.chart G) (Next.Foundations.chart_ok G) _ hz (fun i=>(hUC i).trans (P.large i).need) Z₀
  have hLH (i):uC i ≤ (P.L i).val:=(hUC i).trans (P.large i).need
  obtain ⟨E0,hEarly,-,L0,hcert⟩:=early_for M.K O (Next.Foundations.chart G) I hG (show Early I from fun _=>by simp [I]) hRe hLH (Next.Foundations.chart_ok G)
  obtain ⟨Z,hXE,hUP,heZ⟩:=network E0 hEarly hG Z1
  obtain ⟨aX,hax,hD⟩:= Wait.engine Z hG
  obtain ⟨TP,B,hFA,hA,R,hR,hR₂,hR₃,hR₄,hR₅,⟨b0⟩,⟨h_lei,h_rat⟩,hp,hπ,H₈,⟨S0⟩,htx,hF₁,hF₂,f,h₅⟩:=h₃ q (DelayLe.refl _) D Z aX hax hD
  have hFr : Mallow.FrameAccord R.target P q:= hFb q hwB _ _
  obtain ⟨hp1,H81⟩:=shrink hp H₈ (hle:=show Q1 ≤ Q from hQ')
  choose t ht using fun d=> (aX.fits.deep.eventually_ge_atTop (d+3)).exists
  have ht':∀ d,d+3 ≤ B.a.clock.J (t d):=by rw [hFA]; exact ht
  obtain ⟨N⟩:= UVExtension.Spire.utilize R hG S0
  obtain ⟨Y,hY,hy⟩:= N.exists_bolt
  have hr: UVExtension.Upland.Arc R N Y:=⟨hY,UVExtension.Roads.Unum.commute R (show UVExtension.Roads.Tags.Tax R.shape _ from htx) hF₁ hF₂ hG N,hF₂,hF₁,htx⟩
  have hB':UVExtension.Mast.Lisle t B.a:= UVExtension.Mast.paidLinen t (A:=(Alloy.mk F θ q D Z TP B : Alloy M P)) hl ht' hL
  let Hc:= Mast.cellar N b0 hr t hB'; let Yc := Mast.centerB N hr; let p0 := Mast.roseA N
  let D₁:=UVExtension.Orchard.roof N p0
  let F':= UVExtension.Mast.Cellar.gate p0 Hc
  let S':= Family.mk (Issue.trail Yc) (hol G) (Labels.frames G) (localSection G) t F'
  have hy := UVExtension.Mast.ridge N hr
  have hx0:= UVExtension.Mast.calibrated N b0 hr Hc
  have hc': Spec.Calibrated S':= UVExtension.Mast.Cellar.hardy Hc (UVExtension.Mast.roseA N)
  have hd N' m p hm:= UVExtension.Mast.cliffs N hr m N' p hm
  have hft d N' p (hm:t d ≤N'):=UVExtension.Mast.charts (S:=N) (R:=b0) (U:=Hc) (a:=hr) d N' p hm
  have hi:= h₂ q (hₐ.trans hφ); have hi':=h₂' q hφ
  have hm:= hFA.symm ▸ hA
  have huv:Mix.paidL S':= hm.factorial
  have heg i:(B.a.params i).supportExponent=(100:ℝ):=by
    rw [params_eq B.valid]; change (s.profile (B.a.clock.J i)).supportExponent=100; rw [hv.prices]
  have hp' :∀ i, 100 ≤ (B.a.budget i).supportExponent:=fun i=> (heg i).ge
  have hold := (hδ q (h₁.trans (hₐ.trans hφ)))
  obtain ⟨hx',P',A',hSc⟩:= chaletrail Q b0 Yc t hi hQ hQ' hp hp' hG ht' hy hd hft Kc L V W hV hold hL hl hx0
  obtain ⟨hs',_,_,_⟩:= chaletrail Q1 b0 Yc t hi' (monotone_const) (fun _=>le_rfl) hp1 hp' hG ht' hy hd hft Kc L V W hV hold hL hl hx0
  have ht : Extraction.Wcmain S':= gardena S' (by exact hm.tabs) hx0 hx'.1 hx'.2 hG huv
  obtain ⟨B',HH,hBind⟩:= castle R Yc h₅ (C:=S') rfl (fun i=> (le_max_right ..).trans (hwS.shells i))
  have hres g:= rated (B:=B') hx0 hSc hG ht g hx' Q' hG' M.O (h₄ S' (retains_budget hzd (fun i=>⟨hzL i,hzK i⟩) (hUP.retain B.valid)) B' hBind)
  have hX : Chateau b0 Q Yc t F' D₁:= ⟨ht',hy,hp,hi, hd,hft, hc',hx0,huv,hx',ht, B',HH,hBind,W,P',A',hSc,hres⟩
  have hX1 : Chateau b0 Q1 Yc t F' D₁:= ⟨ht',hy,hp1,hi', hd,hft, hc',hx0,huv,hs',ht, B',HH,hBind,W,P',A',hSc,hres⟩
  have hbarn : Harvest.Barn N b0 Q1 Hc:=by
    refine ⟨hm.tabs,?_,?_⟩
    swap
    · refine ⟨_,_,_,hSc,fun g=>?_⟩
      obtain ⟨u,T,M,S,x,E,I,hs,hB,-⟩:= hres g
      exact ⟨u,T,M,S,x,E,I,hs,hB⟩
    intro v
    let U':= Mast.Cellar.yard v Hc; have hv0:= Vintage.YM.PhysicalNext.Repeat.Legato.chaletrail Q1 b0 (UVExtension.Orchard.ministry N v) t hi' monotone_const (fun _=>le_rfl) hp1 hp' hG ht' (UVExtension.Orchard.housed N v) (fun v' m p hm=> UVExtension.Orchard.routes N v v' p m hm) (Mast.Cellar.freed v Hc) Kc L V W hV hold hL hl (Mast.Cellar.intakeV v Hc)
    obtain ⟨hs,P',T',hQ⟩:=hv0; exact ⟨insured hG t ht' (Orchard.housed N v) (Mast.Cellar.gate v Hc) Kc L V W hV hold hL hl, hs, Vintage.YM.MergeProof.Accent.gardena U' (by exact hm.tabs) (Mast.Cellar.intakeV v Hc) hs.1 hs.2 hG (show Mix.paidL U' from hm.factorial)⟩
  obtain ⟨a₁,hh',hH,h_sh⟩:= Gale.sheaf N b0 h_lei h_rat hr hB'
  have heH : ∀ f:Extraction.Order, CompleteWeak S' f:=by
    have hp:= Next.Rank.East.enclosing (T:=Yc) (Y:=F') hX.freight hx0
    exact hZ' S' (hUP.retain B.valid) B' hBind hx0 hp _ _ _ _ _ _ D₁ hx'
  have he1:=exodus hG b0 Yc Q1 t F' D₁ hX1 hp' H81 hπ
  have he2:=exodus hG b0 Yc Q t F' D₁ hX hp' H₈ hπ
  have hv:Ribbons.Created S':= ⟨_,t,F',rfl⟩
  have hΓ:Acme.Aroma S':= ⟨Ribbons.laurelE S' hG hx' he2 hm.tabs hv hx0,hm.tabs, Ribbons.fugacious S' hG he2⟩
  have hCols: OPE.FramedColumns S' K':=fun d N' per hu m he hm=> (Mast.RG12Joint.stacking N p0 b0 hr t hB' (hBoard k hBC P) d N' per m he hm)
  have hfree : Fridge S' (far B.a) (fly B.a):= freezes hG (fun N' p=>⟨Planned.GuardedAtom.Guard.Keeper.sufficient (hy.born N' p)⟩) (fun i => by
      change step_cost (B.a.params i) ≤ B.a.clock.hatBeta i
      rw [params_eq B.valid i]
      exact (hold _ _ (step_paid _ i) _ (B.valid.pays i)).1)
  refine ⟨_,(congr_arg KernelChoices.penalty (B.valid.kernel.trans hP)).trans hb,hc',hx0,ht,Oasis.survives Hc hr hbarn huv _ hh' hH h_sh h_lei h_rat hX1 he1,?_,?_,hΓ,fun g hg=>⟨grilled S' hx0 hx' hm.tabs hg,heH g⟩, fun g=>by
    obtain ⟨g,A,L,R,z,T,E,h,hp⟩:= hres g; exact ⟨g,A,L,R,T,E,hp⟩⟩
  rotate_left -- LogPackage
  refine ⟨_,_,_, ⟨⟨hx',he2,hCols,hfree,hu' q (hw0.trans (hWb.trans hwB)) Z B.a B.valid,huv,hv,hm.tabs⟩, exodusN hG b0 Yc Q t F' D₁ hX hp' H₈ hπ⟩,exodusL hG b0 Yc Q t F' D₁ hX hp' H₈ hπ hFr,hw' q (hWb.trans hwB) Z B.a B.valid,?_,heg⟩
  refine tendsto_atTop_mono (f:=B.a.clock.J) (fun i=> ?_) B.a.fits.deep
  change B.a.clock.J i ≤ B.a.clock.J (i+1)+1
  exact (B.a.fits.mono i.le_succ).trans (Nat.le_succ _)
  obtain ⟨f,hf,he⟩:= heZ B.a B.valid
  have hV:∀ᶠ i in atTop,f i ≤ i ∧ YM.Pert.Dense.Interior E0 B.a (f i) ∧ B.a.S.a (f i)/B.a.S.a i≤ B.a.clock.hatBeta i:= he.mono (fun i hi=> ⟨hi.1,hi.2.1,hi.2.2.2.2⟩)
  have hSpeed:YM.RG12.Rail.Slugg S'.path.levels:=hSLe _ _ Z (h₁S.trans (hₐ.trans hφ)) B.a B.valid
  have hJ:= YM.RG12.Rail.allLit L0 hcert (hXE.retain B.valid) f hf hV hSpeed (C:=S') hx0 B' hBind (Next.Rank.East.enclosing (T:=Yc) (Y:=F') hX.freight hx0)
  exact ⟨_,hx0,_,hJ⟩
theorem complete_construct {b:ℝ}(h:0<b): ∃ C:Family G, C.path.levels.clock.kernel.penalty=b ∧ Spec.Calibrated C ∧ C.Makes ∧ Extraction.Wcmain C ∧
    UVExtension.Oasis.Floral (hG:=hG) C ∧ (∃ (A:YM.RG12.Commission.Port C) (hC:C.Makes), YM.RG12.Commission.Covered A hC) ∧ (∃ W r D, OPE.Log.LogPackage C W r D) ∧ Acme.Aroma C ∧ (∀ F:Extraction.Order, Cells.CellHyp C F → Grill C F∧MergeProof.East.CompleteWeak C F)∧∀ f:Extraction.Order, ∃ (g:Extraction.Order) (A:Table C.book) (L:ℕ→Table C.book) (R:Bin A) (T:Table C.book) (E:DiffPlan T), Next.Extract.Base C (f.refine g) A L R T E ∧ ∃ s:Spec.Seed C (f.refine g) T,Maxwell.Ranks T s.kernel.spin:=by
   obtain ⟨C,hv,hp,hm,hW,hF,⟨A,hC,lit,hO⟩,hu⟩:= lit_construct hG h
   exact ⟨C,hv,hp,hm,hW,hF,⟨_,hC,hO.covered⟩,hu⟩
-- old API
set_option maxHeartbeats 900000 in
theorem construct {b:ℝ}(h:0<b): ∃ C:Family G, C.path.levels.clock.kernel.penalty=b ∧ Spec.Calibrated C ∧ C.Makes ∧ Extraction.Wcmain C ∧
    UVExtension.Oasis.Floral (hG:=hG) C ∧ (∃ W r D, OPE.Log.LogPackage C W r D) ∧ Acme.Aroma C ∧ (∀ F:Extraction.Order, Cells.CellHyp C F → Grill C F∧MergeProof.East.CompleteWeak C F)∧∀ f:Extraction.Order, ∃ (g:Extraction.Order) (A:Table C.book) (L:ℕ→Table C.book) (R:Bin A) (T:Table C.book) (E:DiffPlan T), Next.Extract.Base C (f.refine g) A L R T E ∧ ∃ s:Spec.Seed C (f.refine g) T,Maxwell.Ranks T s.kernel.spin:=by
  obtain ⟨C,hK,hS,hM,hW,hF,-,hr,H,hi,hj⟩:=complete_construct hG h
  exact ⟨C,hK,hS,hM,hW,hF,hr,H,hi,hj⟩
end YM.PhysicalNext.Repeat.Legato.RG12Joint
