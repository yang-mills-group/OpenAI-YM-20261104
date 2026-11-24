import YM.Integration.WilsonSeparatedOriginalProfileMarch

/-! The full signed original three-copy experiment on its prescribed columns and regulator filter. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalProfileMarket
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open RG05Readout RG05Readout.Address RG05Readout.Native RG05Readout.Many RG05Readout.View RG05Readout.Pulse RG05Readout.Nuclear
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi
open PhysicalNext PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station WilsonLimitConstruction
open WilsonCloseCaptureCalendar Next.Rank RG12 RG17 Extraction Spec Climb Table Trace.Pilot Pier.Lair SharpGram SharpGram.Lenses OPE.Orbits
open WilsonAllDateHarvestFiledReplay WilsonAllDateHarvestNuclearProgram WilsonSeparatedOriginalProfileCut
open scoped Classical BigOperators Topology
universe u
variable {G:Gauge}(R:Run G)(simple:G.Simple){T:Campaign R}(W:Campaign.Pillars R T)
  {δ:ℝ}(fund:FundedOriginalProperties.{u} simple δ W)(book:OPE.Package R.family R.w (mutt R.family.path.levels R.Q) R.doors)
  (portfolio:Funding R)(slow:WilsonWindowReportingPace.Slow R.kit)
variable {order:Extraction.Order}{table:Table R.family.book}{F:Final R.family order table}(L:Layout F)
  {J:ℝ→FamilyBasis (C:=R.family) table}{u:Filter (ℕ×ℕ)}(B:Mantle F u)(E:OPE.Services R.family order table)
  (paid:Pier.Lair.Present F J)(pegs:Pegs B L)
  (near:∀ᶠr in trail,R.family.S.a (L.level r) ≤ r ∧ r ≤ R.family.S.a (L.level r)*R.family.path.levels.clock.hatBeta (L.level r)^2)

def debit (a σ:ℝ):ℝ:=max 1 (a/σ)

theorem price (a:ℝ){σ:ℝ}(positive:0<σ):a*(debit a σ)⁻¹ ≤ σ:=by
  have one:1 ≤ debit a σ:=le_max_left ..
  rw [←div_eq_mul_inv,div_le_iff₀ (zero_lt_one.trans_le one)]
  exact ((div_le_iff₀ positive).1 (le_max_right 1 (a/σ))).trans_eq (mul_comm ..)

def Delivered (s:Fin 3→ℕ)(w:(i:Fin 3)→R.family.label (s i))(Ψ:Wave (Fin 3))(g:Body)
    {n m:ℕ}(nm:n ≤ m)(rank d H k:ℕ)(r η X cap σ:ℝ)(N per:ℕ):Prop:=
  let fee:=(debit (WilsonSeparatedOriginalProfileTariff.budget R.family s n rank r η X cap g) σ)⁻¹
  ∃t:ℕ,N=t+1 ∧ ∃(mt:m ≤ t)(nt:n<t)(tN:t ≤ N),L.level r ≤ N ∧
    ∃P:(i:Fin 3)→Sight R.family (s i) per,Registered R portfolio L s r w n m N per d H P ∧
      Purchases R portfolio L s r η w nm mt tN per d H k P fee ∧
      Settled R portfolio L s w Ψ g rank r η X cap fee σ nm mt nt tN P

include W fund book slow B E paid pegs near in
theorem original (K d:ℕ)(hk:5 ≤ K)(s:Fin 3→ℕ)(degree:∀i,s i ≤ d)(v:(i:Fin 3)→Free R.family (s i))
    (Ψ:Wave (Fin 3))(rank:ℕ){η X cap:ℝ}(sep:0<η)(small:η ≤ 1)
    (grade:(∑i:Fin 3,(s i+2))+4*Fintype.card (Fin 3)<rank+1)(scatter:Scattering Ψ η)
    (xp:0 ≤ X)(sizeX:Tall Ψ (rank+1) 1 X)(cp:0 ≤ cap)(shape:∀z∈tsupport Ψ.val,∀i:Fin 3,‖z i‖ ≤ cap):
    ∃(h:ℕ)(w:(r:ℝ)→(i:Fin 3)→R.family.label (s i))(k:ℕ),
      (∀ᶠr in trail,WilsonReportHarvestReplayPrescribed.Selected R L J s v h r (w r)) ∧
      ∀ᶠn:ℕ in atTop,∀ᶠr in trail,let m:=WilsonMeasuredWindow.stop R.family.path.levels simple K r
      let H:=2*(h+1)+2*(K+1)
      ∃nm:n ≤ m,∀(g:Body)(σ:ℝ),0<σ → ∀l:Filter UVIndex,l ≤ L.lens →
        ∀ᶠz:UVIndex in l,Delivered R portfolio L s (w r) Ψ g nm rank d H k r η X cap σ z.1 z.2:=by
  obtain ⟨h,w,k,names,income⟩:=WilsonAllDateHarvestNuclearProgram.original R simple W fund book portfolio slow L B E paid pegs near K d hk sep s degree v
  refine ⟨h,w,k,names,?_⟩;filter_upwards [income] with n recorded
  have smallR:∀ᶠr:ℝ in trail,r<R.family.S.a n:=(tendsto_id.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds (R.family.S.a_pos n))
  have radii:∀ᶠr:ℝ in trail,0<r:=self_mem_nhdsWithin
  filter_upwards [recorded,radii,smallR] with r funded rp room
  obtain ⟨nm,source⟩:=funded
  refine ⟨nm,?_⟩;intro g σ positive l sub
  let a:=WilsonSeparatedOriginalProfileTariff.budget R.family s n rank r η X cap g
  have one:1 ≤ debit a σ:=le_max_left ..
  apply WilsonSeparatedOriginalProfileMarch.original L (2*(R.family.S.a n*(2*(⌈cap+2⌉₊:ℝ)+1))) ?_ sub
  filter_upwards [source (debit a σ) one] with t bought
  obtain ⟨mt,nt,live,all⟩:=bought
  intro per margin;obtain ⟨P,filed,issue⟩:=all per
  refine ⟨t,rfl,mt,nt,t.le_succ,live,P,filed,issue,?_⟩
  exact WilsonSeparatedOriginalProfileCut.purchased R portfolio L s (w r) Ψ g rank nm mt nt t.le_succ P
    (inv_nonneg.mpr (zero_le_one.trans one)) rp room.le sep small grade scatter xp sizeX cp shape margin filed issue (price a positive)

end YM.Integration.WilsonSeparatedOriginalProfileMarket
