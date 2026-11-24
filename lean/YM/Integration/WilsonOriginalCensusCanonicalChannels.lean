import YM.Integration.WilsonOriginalCensusCanonicalInputs
import YM.Integration.WilsonOriginalCensusCanonicalFields
import YM.Integration.WilsonReceivedCanonicalSocketSeed
import YM.Integration.WilsonOriginalThreeGaussianIncome

/-! Each fixed actual receiver on a genuine copied Wilson board uses the independently posted numerical socket before any sum over children. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusCanonicalChannels
open Function Filter Finset Lattice Wilson Laurent RG Source Labels Marker Multi QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise
open Comparison.RG02 Comparison.RG02.Cumulants Next.SectorChange AllOrder AllOrder.Floe
open PhysicalNext.Repeat.Legato Further.PhysicalPeriodLimitF933 Macrame Shingle
open FVA1Physical.TwoReset WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Embroider WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Soil
open WilsonVacuumPreResetStationaryChange WilsonVacuumPreResetDepositedGeometric
open WilsonOriginalStarSceneWords WilsonThermometerDeclaredSeeds
open WilsonOriginalMixedBlockRows (room)
open WilsonOriginalCensusCanonicalInputs (seed)
open WilsonOriginalCensusCanonicalRows WilsonOriginalCensusCanonicalFields WilsonReceivedCanonicalSocketSeed
open Pressure Push Push.AbsoluteSums Precision Tree Exterior Bloch PowerSeries
open PhysicalForestMarkedRay FVA1Physical.TwoReset
open scoped ContDiff Topology Classical BigOperators Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
private theorem sumJet {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype I]
    (c : I → ℂ) (f : I → E → ℂ) (smooth : ∀ i, ContDiffAt ℝ ω (f i) 0) (j : ℕ) (v : E) :
    Assembly.jet (fun u => ∑ i, c i*f i u) j v = ∑ i, c i*Assembly.jet (f i) j v := by
  let L (i:I) := c i • ContinuousLinearMap.id ℝ ℂ
  have hs (i : I) : ContDiffAt ℝ ω (L i ∘ f i) 0 := (L i).contDiff.contDiffAt.comp _ (smooth i)
  calc
    _ = ∑ i, Assembly.jet (L i ∘ f i) j v := by
      change Assembly.jet (fun a => ∑ i,(L i ∘ f i) a) j v = _
      unfold Assembly.jet
      rw [iteratedFDeriv_fun_sum_apply (fun i _ => (hs i).of_le le_top)]
      simp [smul_sum]
    _ = _ := sum_congr rfl fun i _ => (Assembly.jet_apply_left (L i) (f i) j
      ((smooth i).of_le le_top) v).symm


variable {G:Gauge}{V:Type}[Fintype V][DecidableEq V](R:Run G)(d:V→ℕ){h:V→ℕ}(pt:V→Chamber)
  (q:(j:V)→Choice R d j)(hd:∀j,0 < d j)
  {n:Side}(o:V→Site n)(σ:ℝ)(N i per:ℕ)(hi:i<N)
  (F:Forest (step R i per).ratio)(tag:(step R i per).Choices)(copying:n.val∣(fine R i per).val)
  (x:Affinity.Wallet (room V))(L:Layout G)(tape:Finset Age)(B:fieldDir G (coarse R i per) 1)(z:Precision.Key F G→ℝ)
local notation "M" => row R d q hd o σ
local notation "J" => Stock.census V
local notation "l₀" => d
local notation "Y" => copyColor copying M l₀ (fun j=>(M j).paint x) L tape
local notation "K" => model R N i per hi
local notation "S" => step R i per
local notation "A" => saddle R N i per F
local notation "ρ" => fderiv ℝ ((K).b F) 0
local notation "Pgs" => Fin (Pages n (fine R i per))
local notation "κ" => (fun j=>contact (h j))
variable (addresses:Fin (Pages n (fine R i per)) → V → Lattice.Cover)
  (located:∀p j,wrap (fine R i per) (addresses p j)=(FVA1Physical.TwoReset.copy copying (row R d q hd o σ j) p).center)

include tag located in
theorem original {w:V→ℝ}{width fare:ℝ}{order seats shelf:ℕ}
    (stock:Scene.Armada M w l₀ width fare order seats shelf)(width0:0<width)(legal:Legal tape L)
    (s:Hot (J))(grade:ℕ):
    readJet ((Y).power s+grade) (chartMark (S) F (A) (K) B z (Y) s)=
      ∑p:Pgs,∑j:V,if (J).fire j=s.val then (x j).val*
        seed (h:=h) R d pt q N i per hi F B z addresses p j grade else 0:=by
  classical
  have well:Bulk.Well (Y):=(copy_standard copying M l₀ (fun j=>(M j).paint x) L tape
    (Air.license M _ l₀ w stock width0 (fun j=>stock.honor j x)) legal).1
  let atoms (a:Pgs×V):=raw R d (entry R d a.2 (q a.2))
  let port (a:Pgs×V):=SignedRegisteredKernelPolynomial.primitive (atoms a)
    (wrap (fine R i per) (addresses a.1 a.2)) (stamp R d q a.2)
  let c (a:Pgs×V):ℂ:=if (J).fire a.2=s.val then (x a.2).val else 0
  let f (a:Pgs×V):=Bulk.posed (S) F (port a)
  have ready (a:Pgs×V):ContDiffAt ℝ ω (f a) 0:=SignedRegisteredKernelPolynomial.green F _ _ _
  have computed:Bulk.markFn (S) F (Y) s=fun v=>∑a:Pgs×V,c a*f a v:=by
    funext v
    unfold Bulk.markFn
    rw [Fintype.sum_prod_type]
    change (Y).mark s v.1 (Work.F03.live F v.2)=_
    rw [colored R d q hd o σ copying x L tape]
    apply sum_congr rfl
    intro p _
    apply sum_congr rfl
    intro j _
    by_cases use:(J).fire j=s.val
    · simp only [c,f,port,atoms,Bulk.posed,located p j,if_pos use,WilsonOriginalCensusCanonicalRows.probe]
    · simp [c,use]
  rw [←PhysicalForestMarkedRay.coefficient (S) F (A) (K) B z tag (Y) well s
    (WilsonOriginalJointForestRay.swept R N i per hi F tag),computed,sumJet c f ready,Fintype.sum_prod_type]
  apply sum_congr rfl
  intro p _
  apply sum_congr rfl
  intro j _
  by_cases use:(J).fire j=s.val
  · simp only [c,if_pos use]
    apply congrArg (((x j).val)*·)
    have power:(Y).power s=l₀ j+1:=by
      change Launch.index (J) l₀ s.val +1=l₀ j+1
      rw [←use]
      simp [Launch.index,Stock.census,Census.fire]
    rw [power]
    have cost:=WilsonOriginalStarGradedScene.pole_grade R d (entry R d j (q j))
    rw [site] at cost
    have enough:=Nat.le_succ_of_le cost
    have move:Assembly.translate (Bulk.stage (K) F B) (Bulk.hinge F) z=Bulk.translated (K) F B z:=rfl
    simpa only [f,port,atoms,stamp,seed,Assembly.reading,move] using
      WilsonReceivedCanonicalSocketSeed.kernel (h:=h) R d pt q j (addresses p) N i per hi F tag enough B z grade
  · simp [c,use]

end YM.Integration.WilsonOriginalCensusCanonicalChannels
