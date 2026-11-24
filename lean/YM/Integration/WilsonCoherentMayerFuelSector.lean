import YM.Integration.WilsonCoherentMayerFuelWick
import YM.Integration.WilsonCoherentMayerFuelGate
import YM.Integration.WilsonCoherentMayerOldMarginal

/-! A genuinely deposited positive decoration in the original measured team.
All marked slots precede the one extra inherited-precision head. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonCoherentMayerFuelSector
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

open PhysicalNext.Repeat.Malachite AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open Next.SectorChange WilsonCoherentMayerProjection
open Next.Rank Comparison.RG02.Cumulants Comparison.RG02.Assembly
open WilsonPositionSeparatedProfileMayerWickInputs WilsonRetainedSignedStencilTaylor
open WilsonCoherentMayerHearing Dict06.Series



open WilsonCoherentMayerFuelPolynomial
variable (q:Ledger f 2) (prior:Team R)
def patch:Molecule S:=insert (label (S:=S) q) (prior.signs S)

theorem appended (new:label (S:=S) q∉prior.signs S):
    patch (S:=S) q prior \ prior.signs S={label q} := by
  ext h;simp only [patch,Finset.mem_sdiff,Finset.mem_insert,Finset.mem_singleton]
  constructor
  · rintro ⟨m,n⟩;exact m.resolve_right n
  · rintro rfl;exact ⟨Or.inl rfl,new⟩

variable {p sel:Molecule S} (u:Mayer.Decors sel M) (hsel:sel={label (S:=S) q})
def index:↥sel:=⟨label q,by rw [hsel];exact Finset.mem_singleton_self _⟩

theorem order :
    Mayer.decorOrder u=(u (index q hsel)).val+1 := by
  classical
  apply Finset.sum_eq_single (index q hsel)
  · intro b _ ne
    have joined:∀ t∈sel,t=label (S:=S) q:=by rw [hsel];simp
    have mem:=joined b.val b.property
    exact (ne (Subtype.ext mem)).elim
  · simp

include hsel in
theorem issued (H:Cash W s μ L Q o C T R) (f':Head S→Insert T) (X:Coat T F) (z:Insert.momentSpace X):
    let k:=Mayer.decorOrder u
    Mayer.planned H p u f' X z =
      (∏ h ∈ p\sel,(f' h).joint X z) *
        ((Mayer.exponent H (X.wrapY z.1) z.2 (label q))^k/k.factorial) := by
  dsimp;rw [Mayer.planned,order q u hsel]
  congr 1
  apply Finset.prod_eq_single (index q hsel)
  · intro b _ ne
    have joined:∀ t∈sel,t=label (S:=S) q:=by rw [hsel];simp
    have mem:=joined b.val b.property
    exact (ne (Subtype.ext mem)).elim
  · simp

theorem original (H:Cash W s μ L Q o C T R) (new:label (S:=S) q∉prior.signs S)
    (v:Mayer.Decors (patch (S:=S) q prior \ prior.signs S) M)
    (X:Coat T F) (z:Insert.momentSpace X)
    (first:q.2.1∉F.trunks) (last:arrive q.2.1 q.2.2∉F.trunks):
    let k:=Mayer.decorOrder v
    let y:=X.wrapY z.1
    ((Mayer.planned H (patch q prior) v (Laminate.partner prior H) X z:ℝ):ℂ) =
      ((∏ h∈prior.signs S,(Laminate.partner prior H h).joint X z : ℝ):ℂ) *
        ((WilsonCoherentMayerFuelGate.weight y q R.beta o.a k z.2:ℝ):ℂ) *
          Cloud.paint (fun i=>z.2 (tube y i)) (WilsonCoherentMayerFuelWick.word y q first last k 1) := by
  dsimp only
  have h:=appended q prior new
  rw [issued q v h H]
  have hd:patch (S:=S) q prior \ (patch q prior \ prior.signs S)=prior.signs S:=
    Laminate.compartments prior _ (Finset.subset_insert ..)
  rw [hd,Complex.ofReal_mul,mul_assoc]
  congr 1
  have exactTerm:=WilsonCoherentMayerFuelWick.incidence (X.wrapY z.1) q first last H (Mayer.decorOrder v) 1 z.2
  simpa only [map_one,mul_one,WilsonCoherentMayerFuelGate.weight] using exactTerm

end YM.Integration.WilsonCoherentMayerFuelSector
