import YM.Integration.WilsonPhysicalStationLowerReceiver

/-! Subtracting the measured right-hand reactions kills every actual raised field at that
home. The solved coefficients are taken from the full original lower panel. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationLowerDual
open Function Set Filter Finset Lattice Wilson RG Source Cells GapsContact.Seams Trace.Terrace
open PhysicalNext.Repeat.Legato Extraction RG17 Spec Table Table.Pairing Climb Trace.Pilot PhysMS
open Maxwell Maxwell.Wick XSpace XSpace.Normalize XSpace.Structure1
open MS MS.Land MS.Menus MS.Theater Local.Physical
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonOriginalPublicRelativeGramFreePanel (named pointsAt)
open WilsonPhysicalMeasuredLowerPanel (reported filed)
open WilsonPhysicalMeasuredLowerSolve (grade leg lower)
open WilsonPhysicalStationLowerReceiver (ear point pivot peer gram)
open scoped Classical Topology BigOperators Matrix Matrix.Norms.Operator
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    (J:ℝ→tower S){H:(Bel R.family.book).Hierarchy}{arch:Trace.Terrace.Arch R.family}
    {ℓ:Ultrafilter (ℕ×ℕ)}(B:Deck G)(e:ℕ)(a:Axis)(avoid:Finset E4)
local notation "I" => Glyph B e
private abbrev height (e:ℕ)(_:Unit):Fin (e+1):=⟨e,Nat.lt_succ_self e⟩
local notation "k₀" => grade B e (le_refl e) (height e)
local notation "v₀" => leg R B e (le_refl e) (height e) (fun _=>0)
local notation "G₀" => gram R F J B e a avoid
local notation "peers" => peer R (S:=S) J B e a avoid
local notation "sources" => pivot R F J B e a

theorem registered (r:ℝ)(m:ℕ):
    lower (reported R F J a avoid (k₀) (v₀) m r)=G₀ r m:=by
  ext i j
  rw [WilsonPhysicalStationLowerReceiver.gram,WilsonPhysicalStationLowerReceiver.peer,
    WilsonPhysicalStationLowerReceiver.evaluated]
  simp only [lower,Matrix.submatrix_apply,reported,WilsonOriginalPublicRelativeGramPins.matrix,Fintype.sum_unique,one_mul]
  rfl

def weight (r:ℝ)(m:ℕ)(L:S.Field e→ₗ[ℂ]ℂ):I→ℂ:=(G₀ r m)⁻¹ *ᵥ fun i=>L (sources r i)

theorem reconstruct (r:ℝ)(m:ℕ)(unit:IsUnit (G₀ r m).det)(L:S.Field e→ₗ[ℂ]ℂ):
    ∑j:I,weight R F J B e a avoid r m L j • peers r m j=L:=by
  apply WilsonPhysicalStationLowerReceiver.complete R F J B e a r
  intro i
  simp only [LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul]
  have solved:(G₀ r m)*ᵥ(weight R F J B e a avoid r m L)=fun i=>L (sources r i):=by
    rw [weight,Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ unit,Matrix.one_mulVec]
  rw [←congrFun solved i]
  exact Finset.sum_congr rfl fun j _=>mul_comm _ _

def adjusted {h:ℕ}(eh:e≤h)(r:ℝ)(m:ℕ)(L:S.Field h→ₗ[ℂ]ℂ):S.Field h→ₗ[ℂ]ℂ:=
  L-∑j:I,weight R F J B e a avoid r m (L.comp (F.sector.derivatives.rise eh)) j •
    ear R (S:=S) (e:=h) (point R a avoid m r) (J r e (named R B e j))

theorem cancels {h:ℕ}(eh:e≤h){r:ℝ}(rp:0<r)(m:ℕ)(unit:IsUnit (G₀ r m).det)
    (L:S.Field h→ₗ[ℂ]ℂ)(X:S.Field h)(belongs:X∈LinearMap.range (F.sector.derivatives.rise eh)):
    adjusted R F J B e a avoid eh r m L X=0:=by
  obtain ⟨w,rfl⟩:=belongs
  have clear:point R a avoid m r∈conf 2:=generic_conf 2 (WilsonOriginalPublicRelativeGramAddresses.screened R avoid (pointsAt a) m rp)
  have row(j:I):ear R (S:=S) (point R a avoid m r) (J r e (named R B e j)) (F.sector.derivatives.rise eh w)=peers r m j w:=
    DFunLike.congr_fun (WilsonPhysicalStationLowerReceiver.raised R F eh _ clear _) w
  have paid:=DFunLike.congr_fun (reconstruct R F J B e a avoid r m unit (L.comp (F.sector.derivatives.rise eh))) w
  simp only [LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul,LinearMap.comp_apply] at paid
  simp only [adjusted,LinearMap.sub_apply,LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul,row,paid,sub_self]

/-- Both original regulators precede selection of the actual earlier subtraction or any later target. -/
theorem original (bliss:Bliss F ℓ arch H)(lead:Leading F J)(m:ℝ→ℕ)
    (mesh:Tendsto (fun r=>R.family.S.a (m r)/r) trail (𝓝 0)):
    ∃C:ℝ,0<C ∧∀ᶠr in trail,IsUnit (G₀ r (m r)).det ∧‖(G₀ r (m r))⁻¹‖≤C ∧
      ∀h:ℕ,∀eh:e≤h,∀L:S.Field h→ₗ[ℂ]ℂ,∀X∈LinearMap.range (F.sector.derivatives.rise eh),
        adjusted R F J B e a avoid eh r (m r) L X=0:=by
  obtain ⟨c,cp,_,booked⟩:=WilsonPhysicalMeasuredLowerSolve.original (T:=0) R F J B e a avoid
    (le_refl e) (height e) (fun _=>0) bliss lead m mesh
  refine ⟨c,cp,?_⟩
  filter_upwards [booked,self_mem_nhdsWithin (a:=(0:ℝ))] with r fee rp
  have rank:=fee.1
  have ceiling:=fee.2.1
  rw [registered] at rank ceiling
  exact ⟨rank,ceiling,fun h eh L X found=>cancels R F J B e a avoid eh rp (m r) rank L X found⟩

end YM.Integration.WilsonPhysicalStationLowerDual
end
