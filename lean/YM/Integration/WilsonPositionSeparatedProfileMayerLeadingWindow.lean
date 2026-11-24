import YM.Integration.WilsonPositionSeparatedProfileMayerForced
import YM.Integration.WilsonPositionSeparatedProfileMayerGateGeometry
import YM.Integration.WilsonCoherentMayerColumn

/-! The original full minimal Mayer coefficient on the reported coarse unit.
The common forest and tag average retain every earlier signed occurrence. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonPositionSeparatedProfileMayerLeadingWindow
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open Blaze.March PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt RGLocalTaylor RGLocalTaylor.Insert
open RG01.Survive PhysicalNext.Repeat.Lotus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open PhysicalNext.Repeat.Legato
variable {G:Gauge} {c f L:Side} {S:StepData c f} {T:Tube G S} {F:Forest S.ratio} {R:Rep G f}
    {P:Teller G} {Q:ConnectedActivityE6.Target G P} {W s μ C:ℝ} {o:Target.Order G W}
    {H:Cash W s μ L Q o C T R} {j n l k M:ℕ} {χ:Chi}

open WilsonPositionSeparatedProfileMayerMasks WilsonPositionSeparatedProfileMayerGateReturn
open WilsonCoherentMayerSubmission WilsonCoherentMayerOccurrences WilsonCoherentMayerHearing
open WilsonPositionSeparatedProfileMayerGateSafety LocalTaylorR2.Exponent
private theorem averaged {A:Type} [Fintype A] [Nonempty A] (l r:A→ℝ) {t:ℝ}
    (due:∀i,|l i-r i|≤t):|likely l-likely r|≤t:=by
  have rebase:likely l-likely r=likely (fun i=>l i-r i):=by unfold likely;rw [Finset.sum_sub_distrib];ring
  rw [rebase]
  simpa only [Real.norm_eq_abs] using YM.Merge.Palette.likely_norm (fun i=>l i-r i) t (fun i=>by simpa only [Real.norm_eq_abs] using due i)
variable {run:Run G} {I:Type} [Fintype I] (entry:Submitted run R I) (old:Team R)
variable {r q a Y D' A b B C' ρ e uJ vJ θ K:ℝ}

def read (T:Tube G S) (s:ℝ) (o:Target.Order G W) (χ:Chi):ℝ:=
  likely fun i:Greenbelt.Reserve S=>likely fun tag:S.Choices=>
    let X:=chamber T s o.K χ 1 ∅ i tag
    ∫z,source entry old o.a X z ∂Insert.moment X

theorem measured (fresh:∀m∈old.own,∀i,m.turn≠(row entry i).turn)
    (loc:H.ThinP) (minimal:loc.val=(together entry old fresh).signs S)
    (N:Captain H j C' D' Y B A b r a q n χ) (law:Awning H N.conduit A b ρ e uJ vJ k l)
    (room:Q.goal L s≤K) (allow:Mayer.Approved K θ j M) (inside:authorized H loc.val)
    (cohort:Mayer.Start loc.val) (temp:0≤Pressure.temp s) (stamped:Stamp T) (E:ℝ) (ep:0≤E)
    (paid:∀{F:Forest S.ratio}(X:Coat T F),X.x=s→X.width=o.K→X.manifest→∀U:Support c,
      X.dice.real (eerie X U o.ξ R.beta)≤U.card*E):
    let column:=Laminate.column (together entry old fresh) loc.val H (χ:=χ) M (0:Orders M) (1:Config G c)
    |column-read entry old T s o χ|≤(sites entry T s).card*E*bank entry old ∧
    (∀m∈old.own,∀k,m.turn=Wing.gasKey k→|column|≤(7:ℝ)^4*E*bank entry old):=by
  dsimp only
  have hv:RG.flags (Pressure.temp s) (1:Config G c)=∅:=by
    let i:Greenbelt.Reserve S:=Classical.arbitrary _
    exact ((prism T s χ o.K (1:Config G c) (Greenbelt.allot i)).bowed temp).symm
  have healthy:Healthy (Pressure.temp s) (H.smallAt loc) (1:Config G c):=by
    change Disjoint _ (RG.flags (Pressure.temp s) (1:Config G c));rw [hv];exact Finset.disjoint_empty_right _
  let X (i:Greenbelt.Reserve S)(tag:S.Choices):=chamber T s o.K χ 1 ∅ i tag
  have manifest (i:Greenbelt.Reserve S)(tag:S.Choices):(X i tag).manifest:=by
    change (roster (LocalLTE.Fan.arm (S:=S) ∅)).flags=RG.flags (Pressure.temp s) (1:Config G c)
    rw [LocalLTE.Fan.Field.rosterD];exact hv.symm
  let scored (i:Greenbelt.Reserve S)(tag:S.Choices):=∫z,source entry old o.a (X i tag) z*
    (∏h,gates entry h o.a (X i tag) z) ∂Insert.moment (X i tag)
  have actual:Laminate.column (together entry old fresh) loc.val H (χ:=χ) M (0:Orders M) (1:Config G c)=
      likely (fun i=>likely (scored i)):=by
    rw [received entry old fresh loc minimal N law room allow inside cohort 1 healthy]
    apply congrArg (fun f:Greenbelt.Reserve S→ℝ=>likely f);funext i
    apply congrArg (fun f:S.Choices→ℝ=>likely f);funext tag
    let Z:Coat T (Greenbelt.allot i):=(planted (prism T s χ o.K (1:Config G c) (Greenbelt.allot i)) loc.val).taggedL tag
    have same:Z=X i tag:=by
      dsimp only [Z,X];rw [minimal];exact WilsonPositionSeparatedProfileMayerFlat.same _ χ s o.K temp i tag
    exact congrArg (fun Z:Coat T (Greenbelt.allot i)=>∫z,source entry old o.a Z z*(∏h,gates entry h o.a Z z) ∂Insert.moment Z) same
  have hp:0≤bank entry old:=(norm_nonneg _).trans (bound entry old o.a (X (Classical.arbitrary _) (Classical.arbitrary _)) (1,0))
  rw [actual];constructor
  · apply averaged;intro i;apply averaged;intro tag
    have h:=WilsonPositionSeparatedProfileMayerGateReturn.original entry old (X i tag) H rfl (manifest i tag)
      (WilsonOriginalSignedShutterSquare.blank (T:=T) χ s o.K ∅ i tag) stamped
    exact h.trans (mul_le_mul_of_nonneg_right (paid (X i tag) rfl rfl (manifest i tag) _) hp)
  intro m hm k kind
  obtain ⟨v,live⟩:=(R.activities.forced k).inventory_ne
  rw [←Real.norm_eq_abs];apply YM.Merge.Palette.likely_norm;intro i;apply YM.Merge.Palette.likely_norm;intro tag
  rw [Real.norm_eq_abs]
  have h:=WilsonPositionSeparatedProfileMayerForced.original entry old m hm kind v live (X i tag) H rfl
    (manifest i tag) (WilsonOriginalSignedShutterSquare.blank (T:=T) χ s o.K ∅ i tag) stamped
  have count:(WilsonPositionSeparatedProfileMayerForced.origins S v).card≤7^4:=WilsonPositionSeparatedProfileMayerForced.size S v
  have cast:((WilsonPositionSeparatedProfileMayerForced.origins S v).card:ℝ)≤(7:ℝ)^4:=by exact_mod_cast count
  exact h.trans (mul_le_mul_of_nonneg_right ((paid (X i tag) rfl rfl (manifest i tag) _).trans
    (mul_le_mul_of_nonneg_right cast ep)) hp)

end YM.Integration.WilsonPositionSeparatedProfileMayerLeadingWindow
