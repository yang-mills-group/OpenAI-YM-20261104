import YM.UVExtension.Dales.Rainbow
/-!
 # PRE-PROJECTION Ledger: the E inherited error works IN ANY one-step stanza.

 Distinguish wake/mount input (not literal companion choice) at equal β
 & quantize logRead prior to core branching. Need this theorem before
 reorganizing labels/gluing further reclosures. Hurt → contractor with same
 kernel, even if the two fees arise on other staves. Uses `bonnet.earns` and
 `Tabernacle.reed`, adapted from UVExtension.Dales.Inspire's post-budget
 maps. Does not extrapolate a β coupling germ.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Voucher
open UVExtension
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open PhysicalNext PhysicalNext.Repeat
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof Roost
open Progress.DirectedRecipe Time Rain
open Wick Lamppost YM.UVExtension.Concert
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Guild Tabernacle
open Whirl PhysicalNext.Repeat.Graces
open Oriel Charted Dales Tour
variable {G : Gauge} {X: Metals G} {D:Rolls X.p} {A : Alloy X D} (R:Factor A)
    {N m n : ℕ}{Q ε θ b C W u:ℝ}
local notation "B" => A.B.a
local notation "Y" => A.B.a.clock.hatBeta (m+1)
variable (T:Crest R ε) (H: Tour R N m n ε) (d:Cham A.B.a (m+1) n)
local notation "J"=> A.B.a.clock.J (m+1)
local notation "I" => A.B.a.clock.J m
local notation "s"=> (A.B.a.budget m)
local notation "T'"=> (A.B.a.params m)
local notation "P₀"=> Dales.mount R N (m+1) n 0 (A.B.a.clock.hatBeta (m+1)) 0
local notation "K" => Guild.Market R H.atTopH
local notation "p" => fork (s) G (K).reg (preExponent (s))
local notation "v" => fun x => trill s G (K).reg (preExponent s) x
local notation "σ"=> Time.forecastE A.B.a m
local notation "μ"=> A.B.a.clock.allowance (m+1)
local notation "e"=> Guild.tentPole A m ε
local notation "Z"=> A.B.a.clock.hatBeta m
local notation "φ"=> A.B.kin.alpha N m
variable (h : Paperwork R.shape ε u A.delay) (hk:InsideB (A.B.a.clock.hatBeta (m+1)) C)
variable (r:Fin 4→ Valve (m+1) n A.B.a d) (hr:∀ i,‖place A.B.a (m+1) n d (r i)‖≤ 1)

include T
private lemma worth_nonneg : 0≤ e:= by
   have he:0≤ Time.credit G (X.p.profile (A.B.a.clock.J m)):= (Time.credit_pos ..).le
   change 0 ≤ Yard.basisB * Lamppost.Height ε _ G _; apply mul_nonneg Yard.basis_pos; unfold Lamppost.Height; have hu:= T.positive; unfold δE Clock.gap; positivity

local notation "tv0"=> fun z=> H.cu R d (spent R d r hr h hk z)
lemma tempers : ∃ F:Mark→ Chime (fork (A.B.a.budget m) G (Guild.Market R H.atTopH).reg (preExponent (A.B.a.budget m))), Bumps lever.span F ∧ (∀ z∈lever.span, ‖F z‖ ≤ e)∧ ∀ j:Arbor, F (lever.call j)= vibe (p) (trill (A.B.a.budget m) G (Guild.Market R H.atTopH).reg (preExponent (A.B.a.budget m)) ((tv0) j).logRead):= by
    choose J' hJ using (fun x=>topbar R H d r hr x)
    obtain ⟨_,⟨A'⟩,_⟩ := Guild.earns R H.hm H.atTopH H.W (hp_width R H.hm P₀).1 T H.hr (vi d r) h.gain (notch R h) (staple hk) (fetes R H d r hr) J' hJ
    obtain ⟨F,hF,hf,he⟩:= silk (p) (worth_nonneg R T) A'
    refine ⟨F,hF,hf, fun i=> ?_⟩
    change _ = vibe (p) (trill (s) G (K).reg (preExponent (s)) (Tour.cu R H d (spent R d r hr h hk i)).logRead)
    rw [latched R H d r hr h hk J' i]; exact he i
omit T

def budget_read (x:Valve (m+1) n A.B.a d) (C:ℝ): Tabernacle.Chime (fork (A.B.a.budget m) G (Guild.Market R H.atTopH).reg (preExponent (A.B.a.budget m))) := if hz: Reality A.B.a (m+1) n d x C then vibe (p) ((v) (H.cu R d hz).logRead) else 0
def table (β:ℝ) (x:Flows A.B.a (m+1) n d):= budget_read R H d x.2 (art Y β x.1)
include T h hk
lemma stage : ∃ F,Dales.Order (d:=d) (table R H d C) (e) F:= by
   suffices h':Charted (river A.B.a (m+1) n d) (table R H d C) e by
     obtain ⟨F,hF,hS,hM,hp⟩:= conquest _ (d.weather ..) h'; exact ⟨F,⟨hF,hS,hM⟩,hp⟩
   constructor; intro o hO; let K':= fun i=>(o i).2; have hφ(i): ‖place B (m+1) n d (K' i)‖ ≤ 1:= le_trans (le_max_right ..) ((eddies ..).symm.trans_le (hO i)); have hc(i): |(o i).1| ≤ 1:= le_trans (le_max_left ..) ((eddies ..).symm.trans_le (hO i))
   obtain ⟨F,hF,hS,hx⟩:= tempers R T H d h hk K' hφ
   refine Tabernacle.reed _ _ F hF hS hx hc (fun i hh=>?_); let w:= Rhue _ _ hc hh; unfold table; rw [photo _ o _ hc hh]; unfold budget_read; rw [dif_pos (show _ from spent R d K' hφ h hk w)]
omit h hk
-- REAL ports; no 4-column restriction or only for models arising from some Lives.
variable {x y:Valve (m+1) n A.B.a d}(hx: Reality A.B.a (m+1) n d x C)(hy: Reality A.B.a (m+1) n d y C)
local notation "Y'"=> H.cu R d hx
local notation "μ'"=> (T').width
local notation "ξ"=> Time.forecastK A.B.a m R.scout C
lemma earnMargin : Collection.Local K s (Y') ((1/4:ℝ)*σ) ξ:=by
   let F:= H.oracle R d hx 0; let J':= F.links R H.atTopH
   have hp:= Guild.ready R H.hm H.atTopH H.W H.k _ J' rfl F.related F.price F.aisle rfl T H.hr; obtain ⟨f,hf,hδ⟩:= fleetFund R H.hm T H.atTopH H.W (hp_width R H.hm P₀).1 H.hr _ J' F.related rfl F.aisle F.price
   have hσ:0 ≤ σ:= hp.H_nonneg
   have ht: ∀ i, (s).supBounds ((K).reg i).site ((K).reg i).support ((Y').logRead i) (f i) := fun i=> (hδ i).2
   exact ⟨hp.smooth,hp.family,hp.transforms,⟨f,ht,fun i=>budget_loosen (hf i) (by linarith only [mul_le_mul_of_nonneg_right T.limited hσ])⟩, hp.expensive⟩
private lemma meadow : Meadow.Budget s (K).reg (Y').logRead ((1/4:ℝ)*σ):=by
   have hp:= earnMargin R T H d hx; obtain ⟨f,ha,hM⟩:= hp.cheap; exact ⟨f,hM,fun i=> ⟨hp.smooth i,ha i⟩⟩
omit T
-- compare BEFORE regroup/offset differences. propagate weight thru future
-- proof via native contraction, needing no per-coefficient ℓ assumptions.
section general
variable {R₀ : BudgetPoint} {c:Side}{L : ℕ→ RegularAddress c} {f g: ℕ→ Config G c→ℝ}
lemma merchant {hm:Listing G c}(hg:Meadow.Budget R₀ hm.reg f W) : smoothP R₀ hm.reg f ∧ (fork R₀ G hm.reg (preExponent R₀)).MeasureP (trill R₀ G hm.reg (preExponent R₀) f) W := by
    obtain ⟨k,hk,h⟩:= hg; exact ⟨fun i=>(h i).1,(fork_earns ..).2 ⟨k,fun i=>(h i).2,hk⟩⟩
lemma toll_sub (hf: Meadow.Budget R₀ L f W)(hg: Meadow.Budget R₀ L g u) : Meadow.Budget R₀ L (f-g) (W+u):= by
    obtain ⟨k,hk,h⟩:= hf; obtain ⟨t,ht,hq⟩:= hg
    refine ⟨fun i=> k i+t i, fun i=> ?_,fun i=> ⟨CouplingShape.reg_sub (h i).1 (hq i).1,sup_sub (h i).1 (hq i).1 (h i).2 (hq i).2⟩⟩
    have ha(δ : Prop) [Decidable δ] (u z:ℝ): (if δ then u else 0)+(if δ then z else 0) = if δ then u+z else 0:= by split <;> simp [*]
    simpa only [add_mul,ha] using! budget_plus (hk i) (ht i)
end general
local notation "U₀"=> (H.cu R d hx).logRead
local notation "U'"=> (H.cu R d hy).logRead
local notation "L'"=> place A.B.a (m+1) n d
include h T hk
lemma tend (hv: ‖L' x‖ < rim)(hM: ‖L' y‖<rim): Meadow.Budget s (K).reg ((H.cu R d hx).logRead-(H.cu R d hy).logRead) (e*‖L' x-L' y‖) := by
   obtain ⟨F,hF⟩:= Voucher.stage R T H d h hk
   let A' := river A.B.a (m+1) n d; let V(t: Valve (m+1) n B d):= A' (0,t); have hG : art Y C 0=C:=by simp [art]
   let g f:= vibe (p) ((v) f)
   have ht (t:Valve (m+1) n B d)(hv:‖place _ _ n d t‖<rim): V t∈ Grip:= by
     exact mem_ball_zero_iff.mpr (max_lt (show ‖((0:ℝ):ℂ)‖ < rim by norm_num [rim]) hv)
   have hP (t:Valve (m+1) n B d)(hp:Reality B (m+1) n d t C)(hv:‖place _ _ n d t‖<rim) : F (V t)= g (H.cu R d hp).logRead:= by
     rw [show F (V t)= _ from hF.ray (0,t) (ht t hv)]; unfold table; dsimp only; rw [hG,budget_read, dif_pos hp]
   have he': ‖V x-V y‖= ‖L' x-L' y‖:= by change max ‖((0:ℝ):ℂ)-((0:ℝ):ℂ)‖ ‖L' x - L' y‖= _; rw [sub_self,norm_zero,max_eq_right (norm_nonneg _)]
   have he:= hF.bounds.2.2 _ (ht _ hv) _ (ht _ hM); rw [he',hP _ hx hv,hP _ hy hM] at he; let u:= U₀; let w := U'; let f:=u-w
   obtain ⟨hs,hu⟩:=merchant (meadow R T H d hx)
   obtain ⟨ht,hv⟩:=merchant (meadow R T H d hy)
   obtain ⟨hα,hψ⟩:=merchant (toll_sub (meadow R T H d hx) (meadow R T H d hy)) -- hv overwritten
   have hP: g f = g u - g w:= by
      apply Tabernacle.subPrint (p) _ _ _ _ ⟨_,hψ⟩ ⟨_,hu⟩ ⟨_,hv⟩; intro i k; exact left_sub ((hs i).smooth ((show Concert.Tap s G ((K).reg i).site ((K).reg i).support from k).view) (show Concert.Tap s G _ _ from k).live) ((ht i).smooth _ (show Concert.Tap s G _ _ from k).live) (show Concert.Tap s G _ _ from k).card
   obtain ⟨ν,h₀,h₁⟩:= (fork_earns (K).reg f).1 (Tabernacle.paper (p) ⟨_,hψ⟩ (hP.symm ▸ he)); exact ⟨ν,h₁,fun i=>⟨hα i,h₀ i⟩⟩
end YM.Juniper.Voucher
