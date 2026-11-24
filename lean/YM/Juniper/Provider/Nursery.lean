import YM.Juniper.Provider.Wish
import YM.Juniper.Provider.Rolls
import YM.UVExtension.Oasis.Hall
import YM.OPE.Rough.Supply
/-! # Pin ONE construction, attaching reusable OPE Services & calibration supplies to the UV branch

This is a strengthening under the construction binding of ComparisonCommonWitness.
`Nursery` carries one physical C (named `family`) and its seed data. Local producers
working internally to the constructor can use the data here. Consumer uses must
all be on the SAME C; forgetting back to the shared interface `C,f,T,F` with a
proof about this C will be provided. Branches with similar packings aren't interchangeable.

Adaptation of `Oasis/Hall.lean`, `OPE/Levy/Path`, `Pert/Dense/Kernel`, combining
additional pre-L, Θ delay and Wait requests, with explicit identity to KFactory.
No analytic expansion commitment from this proof. Allows more numerical asks;
as always the analytic justification/sufficiency of particular prices for an
expansion would require proof. Don't instantiate end results on different Nurseries
supplying more asks. Pass the combined asks before choosing the Nursery.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Juniper
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open PhysicalNext PhysicalNext.Repeat
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Legato Legato.Bandage
open InteractingRank Next.Rank Next.Rank.Tapes RankCovariance PhysicalNext.InteractingRank.Soft
open Next.Extract Dash YM.MergeProof MergeProof.Accent East
open UVExtension UVExtension.Harvest
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace

variable {G : Gauge} {hG : G.Simple}

/-- Extra *numerical* reserves. Use `juniper_wishes` instead for even more
   customization. Also interacts with BetaMin in base. -/
structure Extras (G : Gauge) where
  ratios : Metals G → (ℕ → ℝ) → Bid.Worth → ℕ → ℕ
  delay : ∀ (M : Metals G) (P : Rolls M.p), (ℕ → ℝ) → Bid.Worth → ∀ T : Protection P, Delays T
  bar : ∀ (M : Metals G) (P : Rolls M.p) {T : Protection P}, (ℕ → ℝ) → Bid.Worth → Delays T → ℝ
  booster : Legato.Booster G
  wait : ∀ (M : Metals G) (P : Rolls M.p) {T : Protection P} {X : Delays T}, (ℕ → ℝ) → Bid.Worth →
    (D : Bar X) → Wait D

def Extras.plain (G : Gauge) : Extras G where
  ratios _ _ _ _ := 0
  delay _ _ _ _ _ := ⟨fun _ => 0, fun _ _ => 0, fun _ => 1, fun _ => 1⟩
  bar _ _ _ _ _ _ := 2
  booster:= Legato.Booster.bland G
  wait _ _ _ _ _ _ D := cushion D (fun _ => 0) (fun _ => 0) 0

structure Nursery (G : Gauge) (hG : G.Simple) where
  M : Metals G
  P : Rolls M.p
  A : Alloy M P
  X : Roost.Factor A
  U : ℕ → ℝ
  W : Bid.Worth
  b : Legato.Bandage X U W
  B : Org.Bolt A
  t : ℕ → ℕ
  S : Spire.Uses X hG
  arc : Upland.Arc X S B
  L : Mast.Lisle t A.B.a

abbrev Nursery.u (N : Nursery G hG) := Mast.cellar N.S N.b N.arc N.t N.L
abbrev Nursery.family (N : Nursery G hG) := Mast.Cellar.yard (Mast.roseA N.S) N.u
abbrev Nursery.center (N : Nursery G hG) := Mast.centerB N.S N.arc

/-- In particular the doors are pinned to this representation. -/
structure Stock (E : Extras G) (N : Nursery G hG) : Prop where
  ratio_bill : E.ratios N.M N.U N.W ≤ fun j => (N.P.L j).val
  delay_bill : DelayLe (E.delay N.M N.P N.U N.W N.A.θ) N.A.delay
  bar_bill : E.bar N.M N.P N.U N.W N.A.delay ≤ N.A.bar.value
  wait_bill : WaitLe (E.wait N.M N.P N.U N.W N.A.bar) N.A.asks
  powers : PowerRolls N.P
  boosted : E.booster.asks N.X.shape N.A.post N.A.delay
  may_use : Bright.Rhinestone N.X.target N.P
  highest (i k:ℕ) : (N.X.expense i k).wanting= -(7/16:ℝ)
  column : ColumnPre N.M.p N.P
  plenty : Ribbons.Plenty N.family
  slow : Slow N.A.B.a
  chateau : Chateau N.b (fun _ => 1) N.center N.t
    (Mast.Cellar.gate (Mast.roseA N.S) N.u) (Orchard.roof N.S (Mast.roseA N.S))
  harvest : Harvest.Barn N.S N.b (fun _ => 1) N.u
  floral : Oasis.Floral (hG:=hG) N.family
  pack : OPE.Package N.family N.W (mutt N.A.B.a (fun _ => 1))
    (Orchard.roof N.S (Mast.roseA N.S))
  aroma : Acme.Aroma N.family
  rectangles : Pert.Dense.Rectangles N.family
  order : ∀ f : Extraction.Order, Cells.CellHyp N.family f →
    Grill N.family f ∧ OPE.Levy.Stocked N.family f
  support_formula (j : ℕ) : (N.M.p.profile j).supportExponent=100+j

open Pert.Dense in
set_option maxHeartbeats 1200000 in
lemma purchase (E : Extras G) (hG : G.Simple) (β : ℝ) (hβ : 0 < β) :
    ∃ N : Nursery G hG, N.family.path.levels.clock.kernel.penalty=β ∧ Stock E N := by
  obtain ⟨k,hb,hp⟩ := YM.Axial.viable G β hβ
  let v : Orders:= ⟨4,fun i=>6+i,fun i=>2+i,fun i=>100+i⟩
  have hE (i:ℕ): 100 ≤ v.supportExp i:= by change (100:ℝ) ≤ 100+i; simp
  have he : Draft v:= by
    refine ⟨le_rfl,fun i j hij=> Nat.add_le_add_left hij 6,fun i j hij=> Nat.add_le_add_left hij 2,fun i j hij=>?_,fun i=> lt_of_lt_of_le (by norm_num) (hE i),fun i=>by change _ ≤6+i; omega,fun i=>by change _≤2+i; omega⟩
    change (100:ℝ)+i≤100+j; gcongr
  obtain ⟨s,T,Y,K,hX,H,l,hL,hK⟩:= juniper_wishes hG hp he (fun _=>1) (fun _ _ _=>le_rfl) (fun _=>le_rfl) hE E.booster
  have hStage:= H
  have ho:Tendsto (fun i=>(s.profile i).order) atTop atTop:= tendsto_atTop_mono (f:=id) (g:=_) (fun i=> by rw [H.jets]; exact (le_max_right ..).trans (he.k i)) tendsto_id
  obtain ⟨u,hU⟩:= bulletin s (UVExtension.Case.actualPay s T) ho
  obtain ⟨O⟩:= Next.Rank.exists_budget G
  let M:=UVExtension.Case.provider s T (l⊔u)
  obtain ⟨P,hpre,hpower,h_b⟩:= rolls hG M.p (E.ratios M Y K)
  have hz : Pert.Dense.Relay M.p M.K u:=by
     obtain ⟨b,F,ψ,he,v⟩:= hU.bulletin
     refine ⟨b,F,ψ,he,v.same,?_,?_,?_⟩
     · intro i; refine ⟨(v.buys i).1,(v.buys i).2⟩
     · intro i; exact ⟨(v.shops i).1⟩
     intro i d j; exact v.lifts i d j
  let Q (i j:ℕ): JointLoad.Clockwork.Menu:= ⟨Push.SectorMeasure.Chi.canonical,1,0,0,0,0,0,0,one_pos,le_rfl⟩
  let J₀ (i j:ℕ):JointLoad.Folio.Aux:=⟨40,1,1,le_rfl⟩
  let E₀ : Next.Scheduling.Exchange:=⟨0,0,1,1,1,0,0,by norm_num⟩
  obtain ⟨-,H'⟩:= hK (l⊔u) le_sup_left
  obtain ⟨w,h⟩:= H' P
  obtain ⟨F,hF⟩:= h w le_rfl (fun _ _=> ⟨1,1,1,1,le_rfl,zero_lt_one,zero_lt_one⟩) (fun _ _=> E₀)
  obtain ⟨θ,-,hH⟩:= hF _ (fun _=>one_pos)
  obtain ⟨U', h_delay, hu'⟩ := join_delay (E.delay M P Y K θ)
  obtain ⟨V,h₁,hK⟩:= hH Q J₀ U'
  obtain ⟨D,h_D⟩:= Bar.exists_above V (E.bar M P Y K V)
  let I:= E.wait M P Y K D
  obtain ⟨Y',⟨h_ready,h_min,h_window⟩,H⟩:= hK V (DelayLe.refl _) D I
  have hu :∀ i,u i ≤ (P.L i).val:=fun i=>(le_sup_right (a:=l) (b:=u) i).trans (P.large i).need
  obtain ⟨Ynext,hNext,pStage,hRect⟩:=next_wait_for M.K O (Next.Foundations.chart G) Y' hG hz hu (Next.Foundations.chart_ok G)
  let Yin := inflate Ynext
  obtain ⟨a,ha,hp⟩:= Wait.engine Yin hG
  obtain ⟨X,B,hB,R,hShape,c,T,t,S,Hx,Hk,hT,hq,h_v,h_va,h_fr,hD,h_lease,h_rate,⟨hh',hH,h_Φ,h_sh⟩,hE⟩:=
    H Yin (hNext.ready.trans (thicker Ynext).ready) (hNext.range.trans (thicker Ynext).range) (hNext.minL.trans (thicker Ynext).minL) a ha hp
  let W:=Mast.cellar S c Hx t Hk; let S':= Mast.Cellar.gate (Mast.roseA S) W
  let V₀:=Mast.centerB S Hx
  let Z:= Family.mk (Issue.trail V₀) (hol G) (Labels.frames G) (localSection G) t S'
  let D':= Orchard.roof S (Mast.roseA S)
  obtain ⟨hc,hF,hQ,hU,hW,B₀,-,hPrices,K₀,F₀,L,-,H⟩:= hT.reception
  have hpaid : Paid Yin Z.path.levels:=B.valid
  have hrect : Rectangles Z := rectangles Ynext hpaid
    (full _ hRect hG ((thicker Ynext).retain hpaid) hPrices hF (Next.Rank.East.enclosing (T:=V₀) S' hT.freight hF) hU)
  have hv:Ribbons.Created Z:= ⟨_,t,S',rfl⟩
  have hπ:Acme.Aroma Z:= ⟨Ribbons.laurelE Z hG hU h_v hq hv hF,hq, Ribbons.fugacious Z hG h_v⟩
  let N : Nursery G hG := ⟨M,P,Alloy.mk F θ V D Yin X B,R,Y,K,c,T,t,S,Hx,Hk⟩
  obtain ⟨hHalo,hSlow⟩:= (hu' V h₁).2 _ _ hpaid
  refine ⟨N,(congr_arg KernelChoices.penalty (B.valid.kernel.trans hX)).trans hb,h_b,h_delay.trans h₁,?_,
    ⟨h_ready.trans (hNext.ready.trans (thicker Ynext).ready),h_window.trans (hNext.range.trans (thicker Ynext).range),
       h_min.trans (hNext.minL.trans (thicker Ynext).minL)⟩,hpower,hShape.2.2.2.1,hShape.2.2.2.2.1,hShape.2.2.2.2.2.1,hpre,plenty Z hG hpaid (hu' V h₁).1,hSlow,hT,hD,
    Oasis.survives W Hx hD hQ hh' hH (hB.symm ▸ h_Φ) h_sh h_lease h_rate hT h_v,
    ?_,hπ,hrect,fun f hf=>⟨grilled Z hF hU hq hf,hE f⟩,fun j=>hStage.prices _⟩
  · exact h_D
  change OPE.Package Z _ _ D'
  exact ⟨⟨hU, h_v, fun d N p hn=> stacked S c Hx Hk hpre d N p hn, h_fr,hHalo,hQ,hv,hq⟩, h_va⟩
end YM.Juniper
