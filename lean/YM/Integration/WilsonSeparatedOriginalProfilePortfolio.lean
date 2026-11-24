import YM.Integration.WilsonSeparatedOriginalProfileColumn
import YM.Integration.WilsonSeparatedOriginalPairedFolio

/-! A single dated, signed positive conditional portfolio for every center test on the original three-site smooth profile. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonSeparatedOriginalProfilePortfolio
open Function Filter Finset MeasureTheory Lattice Wilson RG Source Extra.Histories Push Local Marker
open MergeProof Accent Menu RG05Readout RG05Readout.Many RG05Readout.Address RG05Readout.Records
open RG05Readout.Native RG05Readout.View GridApprox.Nil WilsonAllDateHarvestPropagation WilsonAllDateHarvestStability
open Bid Pressure Copper Ac Extra.Trajectories PhysicalNext.Repeat Next.Rank.Station Extraction PhysicalNext.Repeat.Legato
open WilsonAllDateHarvestObservedReplay RG05Readout.Nuclear RG05Readout.Pulse RG05Readout.Flatten
open WilsonSeparatedOriginalReplicaScanner WilsonSeparatedOriginalProfileReplay WilsonSeparatedOriginalPairedFolio
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G){n t N per:ℕ}
variable (o:Fin 3→Site (R.family.side n per))(s:Fin 3→ℕ)
variable (S:(i:Fin 3)→Emblems R.family (s i))(x:(i:Fin 3)→Palette R.family (s i))
variable (P:(i:Fin 3)→Sight R.family (s i) per)(roster:Census (Fin 3))
    (full:univ∈roster.choices)(nt:n<t)(tN:t≤N)

def allowed (r η fee:ℝ)(f:Fin 3→Body):Prop:=buy R.family n per o (r*η/2) f ∧
  Filed o (fun _=>(1,false)) s (fun w=>f w.val.1) S x R.makes P roster full nt tN fee

def physical (r:ℝ)(Ψ:Wave (Fin 3))(g:Body)(V:Config G (R.family.side n per)):ℂ:=
  ∫z in Native.box,g.val z*sample R s (fun i=>Launch (m:=t) s S x i N) o (nt.le.trans tN) (nt.trans_le tN) V (cropX Ψ o r z)

theorem original (d k:ℕ)(Q fee:ℝ)(ep:0≤fee)
    {r η X:ℝ}(rp:0<r)(room:r≤R.family.S.a n)(sep:0<η)(small:η≤1)
    (Ψ:Wave (Fin 3))(rank:ℕ)(grade:(∑i:Fin 3,(s i+2))+4*Fintype.card (Fin 3)<rank+1)
    (scatter:Scattering Ψ η)(xp:0≤X)(cap:Tall Ψ (rank+1) 1 X)
    (buying:∀f:Fin 3→Body,(∀i,Tall (f i) (s i+2) 1 1) → buy R.family n per o (r*η/2) f →
      Captured o (fun _=>(1,false)) s (fun z=>f z.val.1) R.makes P S x roster nt.le tN d k Q fee):
    let admit:=allowed R o s S x P roster full nt tN r η fee
    let sale:=WilsonSeparatedOriginalProfileColumn.Posted R o s S x P roster full nt tN fee
    let quota:=earn s R.family n rank η r*X
    ∃L:List (Entry s admit sale),(L.map Entry.rent).sum≤quota ∧
      ∀(g:Body)(V:Config G (R.family.side n per)),flags (R.family.path.rep N per n).p.threshold V=∅ →
        ‖physical R o s S x nt tN r Ψ g V-received g L V‖ ≤ mass g*quota*fee:=by
  intro admit sale quota
  obtain ⟨F,source,jets⟩:=WilsonSeparatedOriginalProfileReplay.purchased o s S x R.makes P roster full nt tN d k Q fee rp room sep small Ψ rank grade scatter xp cap buying
  have issued:Bouquet s Native.box admit F quota:=source
  obtain ⟨L,hL,original⟩:=WilsonSeparatedOriginalPairedFolio.issued issued
    (fun f hf=>WilsonSeparatedOriginalProfileColumn.received R o s S x P roster full nt tN hf.2)
  refine ⟨L,hL,?_⟩;intro g V healthy
  let K:=sample R s (fun i=>Launch (m:=t) s S x i N) o (nt.le.trans tN) (nt.trans_le tN) V
  have exactRead (z:E4)(hz:z∈Native.box):K (cropX Ψ o r z)=K (submitted L z):=by
    rw [original hz];symm;apply WilsonSeparatedOriginalReplicaScanner.same
    exact jets z
  have aggregate:physical R o s S x nt tN r Ψ g V=exposed g L K:=by
    trans (∫z in Native.box,g.val z*K (submitted L z))
    · apply setIntegral_congr_fun Pert.Cellular.cells_compact.measurableSet;intro z hz
      exact congrArg (fun a:ℂ=>g.val z*a) (exactRead z hz)
    · exact WilsonSeparatedOriginalPairedFolio.measured g L K
  rw [aggregate]
  exact (spent g L V K (fun e _=>WilsonSeparatedOriginalProfileColumn.estimate R o s S x P roster full nt tN e.filed V healthy)).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL (positive g)) ep)

end YM.Integration.WilsonSeparatedOriginalProfilePortfolio
