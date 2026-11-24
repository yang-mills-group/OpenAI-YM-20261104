import YM.Integration.WilsonCoherentMayerColumnSample
import YM.Integration.WilsonMeasuredSupportWindow
import YM.Integration.WilsonCoherentMayerPortfolio
import YM.Integration.WilsonCoherentMayerSignedCharge

/-! A retained coefficient of the true two-forest-and-tag averaged marked course. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCoherentMayerColumn
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open Blaze.March PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt RGLocalTaylor RGLocalTaylor.Insert
open RG01.Survive PhysicalNext.Repeat.Lotus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open AnalyticBridge.LocalGaussianLaws PhysicalNext.Repeat.Legato WilsonCoherentMayerGate WilsonCoherentMayerSubmission
open WilsonCoherentMayerSignedCharge (polynomial residual)
open WilsonCoherentMayerColumnSample (prescribed)
private theorem difference {A:Type} [Fintype A] [Nonempty A] (l r:A→ℝ) {t:ℝ} (due:∀i,|l i-r i|≤t):
    |likely l-likely r|≤t:=by
  have rebase:likely l-likely r=likely (fun i=>l i-r i):=by unfold likely;rw [Finset.sum_sub_distrib];ring
  rw [rebase]
  simpa only [Real.norm_eq_abs] using YM.Merge.Palette.likely_norm (fun i=>l i-r i) t
    (fun i=>by simpa only [Real.norm_eq_abs] using due i)

variable {G:Gauge} {c f L:Side}{S:StepData c f}{T:Tube G S}{R:Rep G f}
    {P:Teller G}{Q:ConnectedActivityE6.Target G P}{W s μ C:ℝ}{o:Target.Order G W}
    {H:Cash W s μ L Q o C T R} {j n l k M:ℕ} {χ:Chi}
    {q r a b Y D' v C' A B cost K θ δ ζ:ℝ}
variable (run:Run G) {I:Type} [Fintype I] (entry:Submitted run R I) (old:Team R)
    (fresh:∀m∈old.own,∀i,m.turn≠(row entry i).turn) (taylor:ℕ)
local notation "prior" => together entry old fresh
local notation "lw" => team prior (occupied entry)
variable (loc:H.ThinP)
local notation "base" => Subtype.val loc
local notation "rest" => base\Team.signs prior S
def coat (i:Greenbelt.Reserve S) (tag:S.Choices) : Coat T (Greenbelt.allot i):=
  ((planted (prism T s χ o.K (1:Config G c) (Greenbelt.allot i)) base).taggedL tag)

def model (m:ℕ):ℝ:=
  ∑u∈Finset.univ.filter (fun u:Mayer.Decors rest M=>Mayer.decorOrder u=m),
      likely fun i:Greenbelt.Reserve S=>likely fun tag:S.Choices=>
        let X:=coat (χ:=χ) loc i tag
        ∫ z:momentSpace X,@prescribed G c f L S T (Greenbelt.allot i) R P Q W s μ C o H M base run I _ entry old fresh taylor u X z ∂moment X

theorem submitted (N:Captain H j C' D' v Y A b r B q n χ) (law:Awning H N.conduit A b cost a δ ζ k l)
    (room:Q.goal L s≤K) (allow:Mayer.Approved K θ j M) (contract:∀i z,|entry.phase i z|≤‖z‖) {Ctable:ℝ}
    (receipt:WilsonCoherentMayerOnCourse.At run entry.grade H taylor Ctable)
    (before:(prior).signs S⊆base) (cohort:Mayer.Start base) (inside:authorized H base)
    (empty:roster base=(⟨∅,∅,∅⟩:Stores S)) (temp:0≤Pressure.temp s) (hot:0<R.beta)
    (grade:Orders M) (live:grade.val≤M) (positive:0≤Ctable):
    |Laminate.column prior base H (χ:=χ) M grade 1-model (χ:=χ) (M:=M) run entry old fresh taylor loc grade.val| ≤
      (old.weight*(∏i∈rest,N.conduit.fare i)*Mayer.spreadRate M θ 1^(loc.val.card))*
      (WilsonCoherentReportingPivot.mass run entry.grade R.p.threshold entry.label*(Ctable*(Coat.gStep R.beta)^(taylor+1))):=by
  let g:=Coat.gStep R.beta
  let gain:= WilsonCoherentReportingPivot.mass run entry.grade R.p.threshold entry.label*(Ctable*g^(taylor+1))
  have hm:0≤WilsonCoherentReportingPivot.mass run entry.grade R.p.threshold entry.label:=by
    unfold WilsonCoherentReportingPivot.mass;exact Finset.sum_nonneg (fun _ _=>norm_nonneg _)
  have hg:0<g:=inv_pos.mpr (Real.sqrt_pos.mpr hot)
  have g0:0≤gain:=mul_nonneg hm (mul_nonneg positive (pow_nonneg hg.le _))
  let rate (u:Mayer.Decors rest M):=old.weight*∏i:↥rest,θ*(N.conduit.tag i.val)^((u i).val+1)
  let orders:=Finset.univ.filter (fun u:Mayer.Decors rest M=>Mayer.decorOrder u=grade.val)
  let factual (u:Mayer.Decors rest M):=likely fun i:Greenbelt.Reserve S=>likely fun tag:S.Choices=>
    let X:=coat (χ:=χ) loc i tag
    ∫z,Mayer.planned H base u (Laminate.partner prior H) X z ∂moment X
  let counter (u:Mayer.Decors rest M):=likely fun i:Greenbelt.Reserve S=>likely fun tag:S.Choices=>
    let X:=coat (χ:=χ) loc i tag
    ∫z:momentSpace X,@prescribed G c f L S T (Greenbelt.allot i) R P Q W s μ C o H M base run I _ entry old fresh taylor u X z ∂moment X
  have hv:RG.flags (Pressure.temp s) (1:Config G c)=∅:=by
    let i:Greenbelt.Reserve S:=Classical.arbitrary _
    exact ((prism T s χ o.K (1:Config G c) (Greenbelt.allot i)).bowed temp).symm
  have healthy:Healthy (Pressure.temp s) (H.smallAt loc) (1:Config G c):=by
    change Disjoint _ (RG.flags (Pressure.temp s) (1:Config G c));rw [hv];exact Finset.disjoint_empty_right _
  have read:=Laminate.prescriptive (Y':=prior) χ H loc N law room M grade.val grade allow inside live rfl cohort before 1 healthy
  change Laminate.column prior base H (χ:=χ) M grade 1=∑u∈orders,factual u at read
  let α:=max 1 (max ((M+4:ℝ)*r) ζ)
  have supports:Mayer.Start rest:=fun i hi=>cohort i (Finset.sdiff_subset hi)
  have mid (u:Mayer.Decors rest M) (hu:u∈orders):|factual u-counter u|≤rate u*gain:=by
    apply difference
    intro i
    apply difference
    intro tag
    let X:=coat (χ:=χ) loc i tag
    have clear:Assembly.Clear S X.x X.seeds (Greenbelt.allot i):=by
      change Assembly.Clear S s {(roster base) with flags:=RG.flags (Pressure.temp s) (1:Config G c)} _
      rw [empty,hv]
      exact Assembly.bare_is_Clear S s _
    exact WilsonCoherentMayerColumnSample.issued run entry old fresh taylor u N law room allow contract receipt before
      ((Finset.mem_filter.mp hu).2.le.trans live) supports ((le_max_left _ _).trans (le_max_right 1 _))
      (le_max_left 1 _) ((le_max_right _ _).trans (le_max_right 1 _)) inside X healthy rfl rfl rfl
      (planted_valid _ _) hot rfl clear
  have same:=registered entry old fresh
  have hc:(lw).signs S=(prior).signs S:=census _ _ _
  have money:(lw).weight=old.weight:=by rw [WilsonCoherentMayerCofactor.capital prior (occupied entry) same.1 (regular entry),same.2];rfl
  have small:1*Q.goal L s≤1:=by simpa using room.trans (allow.small.trans (by norm_num))
  have native:=WilsonCoherentMayerPortfolio.account (N:=N) (allow:=allow) (radius:=le_rfl (a:=1))
    (small:=small) (p:=base) lw (by rw [hc];exact before) (by rw [hc];exact supports)
  rw [hc,money] at native
  simp only [one_pow,mul_one] at native
  have rate0 (u):0≤rate u:=mul_nonneg (Finset.prod_nonneg fun a _=>a.profit) (Finset.prod_nonneg fun _ _=>
      mul_nonneg (zero_le_one.trans allow.nonneg) (pow_nonneg (N.conduit.tagged _) _))
  rw [read]
  change |(∑u∈orders,factual u)-(∑u∈orders,counter u)|≤_
  rw [←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑u∈orders,|factual u-counter u|:=Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑u∈orders,rate u*gain:=Finset.sum_le_sum mid
    _ = _ :=(Finset.sum_mul ..).symm
    _ ≤ _ :=mul_le_mul_of_nonneg_right ((Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ orders)
      (fun u _ _=>rate0 u)).trans native) g0

end YM.Integration.WilsonCoherentMayerColumn
