import YM.Integration.WilsonMovingForkOpticalBook
import YM.Integration.WilsonOriginalTwoFlatPublicMixedMesh
import YM.Integration.WilsonAddressedCollarWindow
import YM.SignedWilsonExpansion.Warehouse.Wings
import YM.SignedWilsonExpansion.Fire.Timer
/-! # link to ages from grants. Houses paid with T before.b.G. inspector Serves all date exposures. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.Integration.Election.PRAY.Wings
open RG RG.Supply Extraction PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Table Spec Climb Trace.Terrace Trace.Pilot SignedWilsonExpansion.Homes
open WilsonPhysicalWeakWallStaff.ReStaff WilsonPositionThermometerCapStation WilsonPositionThermometerOrientedStation Next.UVStress Maxwell PhysMS MergeProof.East Next.Rank Next.Rank.East
open Function Filter Lattice Finset Asymptotics
open WilsonCoeffUV.Bank Exporter.Loans WilsonInvariantActionPosition
open SignedWilsonExpansion.Purchases UVClock Schedules SignedWilsonExpansion.Fire
open scoped Topology ContDiff Classical BigOperators
variable {G:Gauge}{R:Run G}{h:G.Simple} {D:ℕ} {p:PRAY R h} (W:p.Wings D)
variable (slow:WilsonWindowReportingPace.Slow R.kit)
variable {I:Type}[Fintype I]
abbrev interval (r:ℝ)(s:I→W.OrderM) :Prop:= ( ∀ i,r≤(s i).val ∧ (s i).val≤2*r ) ∧ ∃ i,(s i).val=r
abbrev pathF (s:I→W.OrderM):= WilsonMovingForkOpticalBook.reporter p.last W.book s
open WilsonThermometerUnitFilingFourPoolClock (outer)
lemma annex : ∀ᶠ r in Trace.Pilot.trail, ∀ s:I→W.OrderM, W.interval r s→∀i,r≤(s i).val ∧ (s i).val≤outer p.Z 1 r:=by
   let g:=Trace.Pilot.wilson p.Z; have hp:= wilson_link p.last h p.bliss.budgets p.bliss.keen p.bliss.lies
   filter_upwards [hp.positive,(hp.conforms h).eventually_le_const ( half_pos zero_lt_one ), self_mem_nhdsWithin] with r hi hv hh s q i; refine ⟨ q.1 i|>.1,le_trans (q.1 i |>.2) (?_)⟩; unfold outer; rw [pow_one,mul_comm (2:ℝ)]; apply mul_le_mul_of_nonneg_left _ (show 0<r from hh).le; rw [ ←one_div ]; apply ( le_div_iff₀ hi ).2; linarith only [hv]
abbrev capU (t r:ℝ) := WilsonCloseCaptureDate.level R.family.S (16*(r+t*r))
lemma brackets (v:ℝ)(hW:0≤v): ∀ᶠ r in Trace.Pilot.trail, R.family.S.a ( capU (R:=R) v r+1) < 16*(1+v)*r ∧ 16*(1+v)*r≤ R.family.S.a (capU (R:=R) v r):=by
   have he:0<16*(1+v):=by positivity
   have hr:Tendsto (fun x:ℝ=> 16*(1+v)*x) Trace.Pilot.trail (𝓝 0):=by simpa only [mul_zero,id_eq] using ((show Tendsto id Trace.Pilot.trail (𝓝 0) from tendsto_id.mono_right nhdsWithin_le_nhds).const_mul (16*(1+v)))
   filter_upwards [ hr.eventually_le_const (R.family.S.a_pos 0),self_mem_nhdsWithin] with i hi hX; unfold capU; rw [show 16*(i+v*i)= 16*(1+v)*i from by ring]; exact WilsonCloseCaptureDate.bracket R.family.S (mul_pos he (show 0 < i from hX)) hi
open Pert.Asymptotics
variable {ι:Type} {L:Filter ι}{r:ι→ℝ}{k v N w:ι→ℕ}{γ ξ:ℕ}{s:ι→I→W.OrderM} {A:ι→ℝ}{U:ℝ}
local notation "J₀"=> R.family.path.levels
local notation "S₀"=> R.family.S
local notation "B₀"=> fun i=> cck G ( r i ) -- issue use parentheses custom maybe
local notation "f₀"=> fun i=> W.pathF ( s i )
variable (hr:Tendsto r L Trace.Pilot.trail)(hs:∀ᶠ i in L,W.interval (r i) (s i))
include W hr hs slow
lemma pages (d:I→ Fin (D+1)) : hereD J₀ r f₀ ≤ᶠ[L] payD B₀ (-1/2) ∧ ∀ᶠ i in L, r i≤ (J₀).clock.hatBeta ( (f₀) i )^(2*W.T+11+2*1)* (S₀).a ((f₀) i):=by
    let farm:= Trace.Pilot.wilson p.Z; let g:= wilson_link p.last h p.bliss.budgets p.bliss.keen p.bliss.lies; have e:∀ᶠ i in L, hereD J₀ r f₀ i≤ farm (r i)^2 ∧ r i≤ (J₀).clock.hatBeta ( (f₀) i )^(2*W.T+11+2*1)* (S₀).a ( (f₀) i ) := (?_) -- replace
    · exact ⟨ ( EventuallyLE.trans (e.mono fun i hi=> hi.1 : hereD J₀ r f₀ ≤ᶠ[L] fun i=> farm (r i)^2) ( owns_clock h hr g ) ), e.mono fun i hi=> hi.2 ⟩
    · filter_upwards [hr.eventually (WilsonOriginalTwoFlatPublicMixedMesh.original p.last h p.bliss slow D W.T 1 d W.book),hr.eventually (annex (I:=I) W), hs] with i hi hv hu; obtain ⟨a, b⟩:=hi _ (hv _ hu) hu.2; obtain ⟨x,hx⟩:=hu.2; exact ⟨a,hx.symm.trans_le (b x)⟩
omit hs slow hr
lemma stoveAt (a:W.OrderM) : R.family.S.a (floorP W a) ≤ a.val :=by
   exact ( WilsonReflectedPublicBulbBerth.mesh R _ ( W.book a ).checked ).trans ( W.book a ).active.le
lemma groundAt (e:I)(s:I→ W.OrderM) : floorP W (s e) ≤ W.pathF s:= WilsonMovingForkOpticalBook.station_le p.last W.book s e ⟨0,by omega⟩ true
include slow hs hr
lemma being (x:I)(z:Glow J₀ r B₀ L f₀) : Glow J₀ r B₀ L (fun i=> floorP W ( s i x )) := by
    have hp :∀ᶠ i in L,0<r i:= hr.eventually self_mem_nhdsWithin; refine star_path h (radius_clock h hr) hp (EventuallyEq.rfl) z (Eventually.of_forall fun i=> groundAt ..) 2 (by norm_num) ( ?_ ); filter_upwards [ hs,hp] with i hi hp; exact (div_le_iff₀ hp).mpr ( (stoveAt W (s i x)).trans (hi.1 x |>.2) )
structure StopT (A:Levels G) (C:Family G)(L:Filter ι)(r:ι→ℝ)(f k v w :ι→ℕ)(γ ξ:ℕ)(U:ℝ)(X:ι→ℝ): Prop where
    ready : ∀ᶠ i in L, A.S.a ( v i + 1) < 16*(1+U)*r i ∧ 16*(1+U)*r i≤ A.S.a ( v i )
    safe : 0 ≤ U
    buried : (fun i=>v i+2)≤ᶠ[L] f
    caught : w ≤ᶠ[L] v
    memory : ∀ᶠ i in L,A.S.a ( v i ) / A.S.a ( w i ) ≤ ( X i^ξ )^2 ∧ A.S.scale (v i)-A.S.scale ( w i ) ≤ 4*(2*(ξ:ℝ)+1)* Real.log ( X i )⁻¹
    turnout : (Glow A r (cck G∘r) L v)→ IsEquivalent L X (needle G ∘ r)
-- burn via quotes
lemma requestAge (d:I→Fin (D+1))(hz:StopT J₀ R.family L r f₀ k v w γ ξ U A)(hk:∀ᶠ i in L,k i= berth R γ ( ( f₀ ) i )) : AgeRead (2*W.T+11+2*1) γ ξ L J₀ r B₀ f₀ k v w A:=by
    obtain ⟨a,x⟩:= W.pages slow hr hs d; have hu:∀ᶠ i in L,0<r i:= hr.eventually self_mem_nhdsWithin; have hr':Rise (cck G ∘ r) L:= radius_clock h hr; refine ⟨a,x,hk.mono (fun i hx=> (WilsonInvariantActionPosition.arrival R _ _).1.le.trans_eq hx.symm),?_, hz.buried,⟨ 16*(1+U),( by linarith only[hz.safe] ), hz.ready.mono fun i hi=>hi.1.le ⟩,hz.caught,hz.turnout,hz.memory⟩
    have u : hereD J₀ r f₀ ≤ᶠ[L] (1:ι→ℝ):= a.trans ( ( payD_cuts hr' (by norm_num: -(1:ℝ)/2< 0) ).eventually_le_const zero_lt_one ); let p' := shutter h hr' hu (EventuallyEq.rfl) u; let f' (i):= W.pathF ( s i ); have hv:Tendsto f' L atTop:= fee_Θ p' J₀ h IsEquivalent.refl; filter_upwards [ hv.eventually (WilsonAddressedCollarWindow.original R h slow γ zero_lt_one), hk ] with i hi hz; rw [hz]; exact ⟨ hi.2.1,(hi.2.2.trans_eq (by rw [ Real.rpow_one, pow_succ ] ))⟩
end YM.Integration.Election.PRAY.Wings
