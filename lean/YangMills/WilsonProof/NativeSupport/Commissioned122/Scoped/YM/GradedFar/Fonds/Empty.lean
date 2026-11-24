import YM.OPE.Sparse.Circuit
import YM.Integration.WilsonPositionHomogeneousFrame
import YM.OPE.Logarithmic
import YangMills.WilsonProof.NativeSupport.Commissioned122.Scoped.YM.GradedFar.G6.Child
import YM.OPE.Orbits.System
import YM.TraceExtension.Atlas.Sink
import YM.PhysMS.Foundation.Estimates
import YM.OPE.Orbits.Inclusions
import YM.AllOrder.Leading.Solve
import YM.GapsContact.Earn.Cliff
import YM.OPE.Log.Measuring
import YangMills.WilsonProof.NativeSupport.Commissioned122.Scoped.YM.GradedFar.PricedRows
import YM.WiderProfiles.Basket
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import YangMills.WilsonProof.NativeSupport.Commissioned122.Scoped.YM.GradedFar.Toward.Original
/-!
# The empty unit throughout this *actual* horizon
Use SignedScalarReader.packet_units and WilsonPositionScaleLawGuardUnit proof,
shipped as port with simpler imports. At true F. Even empty arrays of Sec.
Thread same unit choices of all compacts (through all needed h).
-/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 500000
noncomputable section
namespace YM.FVA2.GradedFar.Fonds
-- scope names of those sources
open Function Filter Set Spec Table Extraction Climb PhysMS Trace.Pilot Maxwell Maxwell.Free XSpace XSpace.Normalize
open OPE OPE.Orbits PhysicalNext.Repeat.Legato MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival PowerSeries
open Integration
open scoped Topology Classical BigOperators Asymptotics Polynomial
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)(J:ℝ→tower S)
    (Z:Register.WilsonPrescription G)(Q: Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
private theorem named (C:Family G)(d:ℕ):fields C.labels d ((Bel C.book).unit d)=leaf G d:=Subtype.ext (unit_address C.labels d)
private theorem seat (C:Family G)(d:ℕ)(a:Change G d)(h:Bijective (stand a)):
    ((fields C.labels d).trans ((LinearEquiv.ofBijective (stand a) h).trans (fields C.labels d).symm)) ((Bel C.book).unit d)=(Bel C.book).unit d:=by
  apply (fields C.labels d).injective; change fields C.labels d ((fields C.labels d).symm (stand a (fields C.labels d ((Bel C.book).unit d))))=_; rw [LinearEquiv.apply_symm_apply,named,solitary]
private theorem positioned (d:ℕ)(r:ℝ):WilsonPositionPrescribedFrame.change F J Z.store d r ((Bel R.family.book).unit d)=(Bel R.family.book).unit d:=by
  unfold WilsonPositionPrescribedFrame.change; split
  · exact seat R.family d _ _
  rfl
local notation "W" => WilsonPositionHomogeneousFrame.homogeneous F J Z
private theorem moving (d:ℕ)(r:ℝ):WilsonPositionHomogeneousFrame.change F J Z d r ((Bel R.family.book).unit d)=(Bel R.family.book).unit d:=by
  unfold WilsonPositionHomogeneousFrame.change; split
  · exact seat R.family d _ _
  rfl
private theorem packet_units {I : Type} [Fintype I] {d : I → ℕ} (x : I → E4) (o : E4){D:ℕ}
    (hx : ∀ k ≤ D, orbitMargin Q.port k x o) :
    Q.packet D x (fun j => S.unit (d j)) o = S.unit D := by
  rw [← F.sector.derivatives.fixs Q.lifts F.room.kernel.laws (Nat.zero_le D), ← Q.reconstruct D 0 (Nat.zero_le D), Reader.packet]
  apply Finset.sum_congr rfl; intro k _; apply congrArg (F.sector.derivatives.rise (d := k.val) (Nat.le_of_lt_succ k.isLt))
  exact Sparse.Circuit.fill F Q (w := fun j => (⟨d j, S.unit (d j)⟩ : S.Tag)) (fun _ => rfl) (hx k.val (Nat.le_of_lt_succ k.isLt))
open O.Score Compare
-- no norm assumptions outside leg budgets; simply use every cost
variable (h:ℕ)
lemma no_unit_price (l:Leading F J): ∀ᶠ r in trail,∀ v:Sec G h,v=leaf G h→ field W r h v = S.unit h := by
   filter_upwards [l.unit h] with r s v hv; subst v; rw [← named R.family]
   unfold field; rw [LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply]
   change J r h (WilsonPositionPrescribedFrame.change F J Z.store h r (WilsonPositionHomogeneousFrame.change F J Z h r ((Bel R.family.book).unit h)))=_
   rw [moving,positioned,s]
lemma vacant (d:Fin 0→ℕ)(p:Leading F J){M δ:ℝ}(t:0<δ)(g:0≤M) : ∀ᶠ r in trail,∀ x:Points 0,∀ o:E4,∀u:Appointed122Fields G d, cW F W r o x u Q h=leaf G h := by
   filter_upwards [admissible_separated (I:=Fin 0) F Q g t h,no_unit_price F J Z h p] with r c h' x y u
   apply (field W r h).injective; rw [h' _ rfl,cW,LinearEquiv.apply_symm_apply]
   rw [show labels W r u=(fun i=> S.unit (d i)) from funext fun i=>i.elim0]; exact packet_units F Q _ _ (c (place y r x) y ⟨fun i=>i.elim0,fun i=>i.elim0⟩)
end YM.FVA2.GradedFar.Fonds
