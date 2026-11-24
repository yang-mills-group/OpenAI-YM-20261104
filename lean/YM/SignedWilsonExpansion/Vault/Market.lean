import YM.SignedWilsonExpansion.Vault.Tour
import YM.SignedWilsonExpansion.Warehouse.Election
import YM.SignedWilsonExpansion.Warehouse.Wings
import YM.Integration.WilsonReflectedMixedPrescribedSchool
import YM.SignedWilsonExpansion.Warehouse.Tide
/-! # receipt for election and identified slot bank. b path clamps independent before lengths. 
 Supporting full mixed registration at two r, choose dummy g=0 for unspent branch. Always b prior.
 `/pair.wave` Earnings. Weight.No perturb shape or term used in appointment.
-/
set_option autoImplicit false
set_option maxHeartbeats 540000
noncomputable section
namespace YM.Integration.Election.VaultM
open Function Set Filter MeasureTheory Extraction Climb Spec Table Next.UVStress Trace.Pilot PhysMS Maxwell Extra.FD
open RG.Supply PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Table Spec Climb Trace.Terrace Trace.Pilot
open SignedWilsonExpansion SignedWilsonExpansion.Homes Lattice Wilson WilsonCoeffUV WilsonCoeffUV.Bank RG PowerSeries SignedWilsonExpansion.Purchases UVClock Schedules
open XSpace Commission Dancer Dancer.Drawing Dancer.Shell Dancer.Fort Dancer.Stitch Camera SignedWilsonExpansion.Vault
open Asymptotics Precision XSpace.Normalize
open FVA2 FVA2.Dframe XSpace.Cirrus FVA2.Register
open scoped Topology ContDiff Classical BigOperators ENNReal
open PRAY
variable {G:Gauge}{R:PhysicalNext.Repeat.Legato.Run G}{h:G.Simple}{e:Axis}{T₀:Campaign R}{W₀:Campaign.Pillars R T₀}
variable {P:PRAY R h}{D:ℕ}(W:P.Wings D)
universe u
variable {σ:OrderS G}{ε:ℝ}(p:PaidP.{u} e h ε σ R T₀ W₀) (Z:WilsonPrescription G) (b:Scarf G D)
open WilsonOriginalTwoFlatPublicNamedFare
abbrev fieldW (x:Scarf G D) (s: W.OrderM) (_ y:Bool):P.S.Field ( SlotX x ).val:= chosen P.last P.J Z s.val (W.V s ( SlotX x )) y ( pre R.family ( clothD x )) 0 -- dummy x expr at bool false
include W p
lemma litMarket (hv:0<D) : ∃ t≥D+3, WilsonReflectedMixedPrescribedSchool.Enrolled P.last D W.T 1 t SlotX W.book (fieldW W Z):=by
     letI : Nonempty (Scarf G D):=⟨ Draft.headR hv false ⟩
     obtain ⟨t,ht,hP⟩:= WilsonReflectedMixedPrescribedSchool.nominated (I:= Scarf G D) P.last P.J Z h P.bliss p.receiptsP.2 p.tuition (fun i=>by rw[p.paid.support];norm_num ) (fun i=>by rw[p.paid.support]) p.way.paid.stoves P.VFrame.2 P.VFrame.1 D
     exact ⟨t,ht,hP W.T 1 SlotX _ _ W.book⟩
omit p
abbrev identifies (s: W.OrderM) (b:Scarf G D):= streak (W.lit s) ( clothD b )
lemma TH (s:W.OrderM)(N:ℕ×ℕ) : ((( W.book s ).rows ( SlotX b )).arm true (fieldW W Z b s true true)).source N= identifies W s b N.1 N.2:=by
     unfold fieldW WilsonOriginalTwoFlatPublicNamedFare.chosen; simp only [Wings.V]; rw [ WilsonPositionProgramPublicStations.Pair.weak, if_pos (show true=true from rfl),LinearEquiv.symm_apply_apply ]; unfold identifies streak BeamT.microphone; rw [dif_pos (( live b ).2.trans ( W.book s ).fits)]; rfl
section
variable {ι:Type}{L:Filter ι} (s:ι→W.OrderM) {r:ι→ℝ}
open Wings
noncomputable abbrev ramp (U:Store G): Shawl R.family P.S ι ( P.W U ):= ⟨fun i=>(s i).val,W.lit∘s,fun i d=> if v:d≤D then W.V (s i) ⟨d,Nat.lt_succ_of_le v⟩ else P.W U (s i).val d⟩
lemma scribe (U:Store G)(hr:Tendsto r L trail)(hp:pivotT L r (fun i=>(s i).val)): Shine (f:=P.f) ( P.W U ) P.H ( ramp W s U ) P.Y r L D:=by
     have he:= ( compare_pivot hr hp ); have hu:= W.actualB L s he.1; let A:= ramp W s U; have hŋ (t:ℕ)(ht:t≤D)(i:ι):A.capacity ( P.W U ) i t=W.WingSpan (s i) ⟨t,Nat.lt_succ_of_le ht⟩ U :=by unfold Shawl.capacity A ramp; dsimp only; rw [dif_pos ht]
     refine ⟨hp,hu.1,hu.2,fun t ht=> (W.pivots L s he.1 U).mono fun i hi=> hŋ t ht i ▸ hi ⟨ t,Nat.lt_succ_of_le ht⟩,fun {t} ht x=>( W.oriented L s he.1 U ⟨t,Nat.lt_succ_of_le ht⟩ x ).congr (fun i=> congr_arg (fun z: _ ≃ₗ[ℂ] _=> z x ) ( hŋ t ht i ).symm ),fun {t} ht=> Eventually.of_forall fun i x=> ?_ ⟩
     unfold ramp; dsimp only; rw[dif_pos ht]; exact W.ink (s i) ⟨ t,Nat.lt_succ_of_le ht⟩ _
-- Curtains.L ∆.
lemma marquee (f:ι→ℝ)(h:Tendsto f L trail): ∃ s:ι→ W.OrderM,f=ᶠ[L] fun i=>(s i).val:=by
      let g (i:ι):W.OrderM:= if p:0<f i∧ f i<W.δ then ⟨f i,p⟩ else ⟨W.δ/2,half_pos W.pos,half_lt_self W.pos⟩
      refine ⟨g,?_⟩; filter_upwards [h.eventually self_mem_nhdsWithin,(h.mono_right nhdsWithin_le_nhds).eventually_lt_const W.pos] with i hi hp; exact (congrArg Subtype.val (dif_pos (show 0<f i ∧ f i<W.δ from ⟨hi,hp⟩):g i = ⟨f i,⟨hi,hp⟩⟩)).symm
structure Diary (W:P.Wings D)(L:Filter ι)(r t:ι→ℝ) where
     home : Bool→ι→W.OrderM
     lo : (fun i=>( home false i).val)=ᶠ[L] r
     hi : (fun i=>( home true i).val)=ᶠ[L] t
     holds : ∀ a:Bool, pivotT L r (fun i=>( home a i).val)
variable (t:ι→ℝ)
lemma shelfDiary (hr:Tendsto r L trail)(h:pivotT L r t) : Nonempty ( Diary W L r t ):=by
     obtain ⟨s, hs⟩:= marquee W r hr; obtain ⟨y,hU⟩:= marquee W t (compare_pivot hr h |>.1); let z(b:Bool):ι→ W.OrderM:=b.rec s y; refine ⟨ z, hs.symm,hU.symm,fun b=>?_⟩; cases b; · filter_upwards [hs,hr.eventually self_mem_nhdsWithin] with i hi hp; rw[← show r i=(z false i).val from hi]; refine ⟨le_rfl,?_⟩; linarith only [(show 0< r i from hp)]
     filter_upwards [h,hU] with i hi hp; exact ( show t i=(z true i).val from hp ) ▸ hi
end
end YM.Integration.Election.VaultM
end
