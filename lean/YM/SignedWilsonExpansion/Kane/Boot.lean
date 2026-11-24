import YM.SignedWilsonExpansion.Kane.Finale
import YM.Integration.WilsonPositionHomogeneousComparison
/-!
# Homogeneous prescription compatibility & purchase at any fixed horizon
Heavy Presentation.Reader. Keep one K,t.
-/
set_option autoImplicit false
set_option maxHeartbeats 480000
noncomputable section
namespace YM.Integration.Election
open RG RG.Supply Extraction PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Table Spec Climb Trace.Terrace Trace.Pilot
open Function Filter Lattice Wilson Source
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1 FVA2 FVA2.Scale.Level Future
open SignedWilsonExpansion.Belfry SignedWilsonExpansion.Belle SignedWilsonExpansion.Dancer SignedWilsonExpansion.Belfry.Crisis SignedWilsonExpansion.Belfry.Classroom SignedWilsonExpansion.Belfry.ScaleFits
open SignedWilsonExpansion.Kane.Tilted Scale MS MS.Native MS.High MS.Land MS.Fleet Asymptotics
open PhysMS Frame Order Spin Next.UVStress OPE OPE.Orbits
open private leg from YM.Integration.WilsonPositionHomogeneousFrame
open PowerSeries Register
open scoped BigOperators Topology Classical ContDiff
variable {G:Gauge}{R:Run G}{h:G.Simple}
-- shoe adapter & post. do not identify clocks by convergence theorem only.
namespace Frames
variable {n d b j:ℕ} {ι:Type} {l: Filter ι} {f:Extraction.Order} {S:Table R.family.book}(F:Final R.family f S)(J:ℝ→tower S)
variable (lead : PhysMS.Leading F J){V:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}{Q:MS.Land.Prescription (Press.portDeck G)} (Z:WilsonPrescription G){dial:Bool}(H: Main.Match Z h V Q dial)
local notation "W"=> WilsonPositionPrescribedFrame.positioned F J Z.store
local notation "Θ"=> WilsonPositionHomogeneousFrame.reading F J Z
local notation "A"=> Measure.adjust Z.scheme Z.criterion d
local notation "κ"=> WilsonPositionHomogeneousFrame.turn F J Z
lemma matchesT : Θ=SignedWilsonExpansion.Kane.Tilted.Date F Z.criterion W :=rfl
lemma testament : WilsonPositionThermometerReading.tested F W Z.criterion=SignedWilsonExpansion.Kane.Tilted.Temp F Z.criterion W:=rfl
lemma Shoe (hL:Leading F J) : SignedWilsonExpansion.Kane.Tilted.Shoe F W Z.store where
   gleans d:= ⟨fun r=> WilsonPositionPrescribedScreen.hierarchy F W d r,fun n φ t=> Filter.Eventually.mono RG17.positiveLength fun r p=> Eq.symm ( WilsonPositionPrescribedScreen.actual F W d n φ t p ),WilsonPositionPrescribedFrame.original F J Z.store hL d⟩
local instance fieldEnd : FiniteDimensional ℝ (FieldEnd G d):= Module.Finite.trans ℂ _
open WilsonPositionHomogeneousNear WilsonPositionHomogeneousCoefficients
abbrev Native (r:ℝ)(d:ℕ) : FieldEnd G d:= stand ( field Z d r ) -- r = thermo
lemma convert (b:ℕ)(i:ℝ)(h:Warrant Z) : young b i A=1+ (∑ j∈Finset.range (b+1),i^j • (letter Z d j).val):=by
    induction b with
    | zero => rw [yearP]; simp only[zero_add,Finset.range_one,Finset.sum_singleton, WilsonPositionHomogeneousCoefficients.letter,if_pos rfl,if_true,Submodule.coe_zero,smul_zero,pow_zero,one_smul, add_zero, (h.scheme d).scale.zero ]
    | succ k ih=> rw [ yearP, Finset.sum_range_succ _ (k+1), Finset.sum_range_succ _ (k+1), ←yearP,ih,add_assoc ]; rw [positive Z h d (Nat.succ_ne_zero k), ←Complex.ofReal_pow, show ∀ x:FieldEnd G d,(↑( i^(k+1) ):ℂ) • x= ( i^(k+1) ) • x from fun x=> IsScalarTower.algebraMap_smul ℂ ( i^(k+1) ) x ]
-- numerical N(t) sal dual certification. standard proof read ∥point projection∥.
include H
lemma implementation {v:ι→ℝ} (h:Tendsto v l (𝓝[>] 0)) : Crisis.Implements Z.scheme Z.criterion l (fun i d=>Native Z ( v i ) d) v :=by
     let X:Store G:= Z.store; constructor; intro d b; let M:= MoveSpace G d; let F':=Measure.adjust Z.scheme Z.criterion d; let u(i:ι):=young b (v i) F'; let N(i):= guide G d ( field Z d (v i) ); let ζ(i):=∑ j∈ Finset.range (b+1), v i^j • guide G d (letter Z d j)
     obtain ⟨A₀,h0,L⟩:= WilsonPositionHomogeneousNear.expansion Z d b; let H₀:= h.mono_right nhdsWithin_le_nhds
     have hE: (fun i=> N i - ζ i)=O[l] fun i=>v i^(b+1):= by
        refine IsBigO.of_bound A₀ (?_); filter_upwards [ h.eventually self_mem_nhdsWithin,h.eventually L] with i hp hQ; rw [ Real.norm_eq_abs,abs_of_pos (pow_pos (show 0<v i from hp) _ ) ]; exact hQ
     intro S; let C':MoveSpace G d→L[ℝ]ℂ:= LinearMap.toContinuousLinearMap ( (( S.restrictScalars ℝ ).comp (Submodule.subtype ( Normalize.Change G d ))).comp (guide G d).symm.toLinearMap ); have ht:= (( C'.isBigO_id _ ).comp_tendsto Filter.tendsto_map ).trans_isLittleO ( hE.trans_isLittleO ( Wipe.expense H₀ IsEquivalent.refl (Nat.lt_succ_self b) ) ); refine ht.congr_left fun i=>?_; change S (↑((guide G d).symm (N i-ζ i)):FieldEnd G d)=S ( Native Z ( v i ) d-young _ _ _ ); unfold N ζ Native; simp only [map_sub ( guide G d ).symm,map_sum,map_smul,LinearEquiv.symm_apply_apply, Submodule.coe_sub,Submodule.coe_sum,Submodule.coe_smul_of_tower]; rw [ convert Z _ _ (purchased Z H) ]; apply congr_arg S; change ((Normalize.Change G d).subtype) (_ - _)=_; rw [map_sub ((Normalize.Change G d).subtype),map_sum]; simp_rw [ map_smul ]; unfold stand; abel
variable (v:ℝ→ℝ)(r:ι→ℝ)(q: Tendsto r l trail)
-- elected enrollment.Sch
variable {Y:(Bel R.family.book).Hierarchy}(p:∀d:ℕ,∀ᶠ i in trail, obedient F Y (J i) d)
variable (issued:Coupling G ( WilsonPositionHomogeneousFrame.reading F J Z ))
include q issued
omit p
lemma mature : Implements Z.scheme Z.criterion l (fun i d=> Native Z (Θ (r i)) d) ( Θ ∘ r ):= implementation Z H ( tendsto_nhdsWithin_iff.mpr ⟨ ( issued.conforms h ).comp q, q.eventually issued.positive⟩ )
local notation "K"=> WilsonPositionHomogeneousFrame.homogeneous F J Z
-- K fame everywhere. Does not convert physical charges.There no role equality before orientation.
omit issued H
include lead p h -- simple
lemma postP (d:ℕ) : ∀ᶠ i in l,∀ x, walk K ( r i ) d x=walk W ( r i ) d (Native Z (Θ ( r i )) d x):=by
    filter_upwards [q.eventually (WilsonPositionHomogeneousFrame.fitted F J Z lead p h d)] with i hi x; exact congr_arg ( W ( r i ) d ) ( leg F J Z hi x )
-- coherence every fixed cap incl unit & reflection at the viewer; true station & hierarchies remain.
include H
omit q
lemma rise (b d:ℕ)(u:b≤d) : ∀ᶠ i in trail,∀ x, walk K i d ( Normalize.up u x )=F.sector.derivatives.rise u ( walk K i b x ):=by
    induction u with
    | refl=> refine Eventually.of_forall fun i x=> (?_); exact ( F.sector.derivatives.arrival F.room.kernel.laws.toSymmetric F.phase.transport.injection _ ).symm
    | @step d u ih=> filter_upwards [ ih, WilsonPositionHomogeneousFrame.adjacent F J Z lead p h ( purchased Z H ) d ] with i hi hv x; change K i (d+1) ( ( Free.fields _ _ ).symm ( XSpace.Normalize.step d ( Normalize.up u x ) ) ) = _; rw [ WilsonPositionPrescribedNested.included, hv ]; change F.sector.derivatives.rise _ ( walk K i d ( Normalize.up u x ) )=_; rw [hi,F.sector.derivatives.transit F.room.kernel.laws.toSymmetric F.phase.transport.injection ] -- arrival.R≥
variable (L:Leading F ( WilsonPositionPrescribedFrame.positioned F J Z.store ))
include L q
omit H
lemma spins (d:ℕ): ∀ᶠ i in l, walk K ( r i ) d ( Normalize.leaf G d )= S.unit d ∧ (∀ x:Sec G d, walk K (r i) d ( reel d x )= S.conj F.room.kernel.spin d (walk K (r i) d x)) ∧ ∀ (s:Signed)(x:Sec G d),walk K (r i) d ( ori s.ortho d x )=S.mirror F.room.kernel.spin d s (walk K ( r i ) d x) := by
    filter_upwards [ SpinW L q d, postP (h:=h) F J lead Z r q p d ] with i ⟨v,p,s⟩ u; unfold Native at u; simp_rw [u]; exact ⟨ by rw [Normalize.solitary,v],fun x=> by rw[←stood_reel,p], fun z x=> by rw [ ←stood_ori, s] ⟩
end Frames
end YM.Integration.Election
