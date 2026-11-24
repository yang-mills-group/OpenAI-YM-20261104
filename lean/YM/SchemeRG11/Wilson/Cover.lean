import YM.SchemeRG11.Wilson.Compare
import YM.Pert.Align.Schedule
import YM.Pert.Fourier.Source
/-! Cover propagators: massless and transversality identities off-diagonal used at CT restoration. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11.Catch
open Lattice Function Filter Asymptotics Pert Full Band Topology Align
open MeasureTheory Metric Set
open Cellular
open scoped Classical BigOperators ENNReal
variable {n : Side}
lemma Medium.constant (T : Itinerary) (z : Cover) : Medium T (fun _ => z):= by
 refine ⟨1,?_⟩
 filter_upwards [T.cutoff.eventually (gt_mem_nhds (show 0<(diam z+1:ℝ)⁻¹ from by positivity))] with i hi
 simpa using (inv_le_inv₀ (show 0<(diam z+1:ℝ)⁻¹ by positivity) (T.positive i)).2 hi.le
lemma Medium.unwrap {T : Itinerary} {z : ℕ→Cover}(hz : Medium T z): ∀ᶠ i in atTop, Lattice.lift (wrap (T.period i) (z i)) = z i := by
 obtain ⟨k,hk⟩:= hz; filter_upwards [hk,(T.huge k).eventually (eventually_gt_atTop 2)] with i hi ht
 apply lift_eq_iff.mpr ⟨rfl,?_⟩; intro j
 have he:= castabs (z i) j
 have h: (2:ℝ)*|(z i j:ℝ)| < ((T.period i).val:ℝ) := calc
   _ ≤ 2*((T.gap i)^k)⁻¹ := by rw [zpow_neg,zpow_natCast] at hi; linarith
   _ < _ := (div_lt_iff₀ (pow_pos (T.positive i) _)).2 ht
 obtain ⟨ha,hb⟩:=abs_lt.mp (show |(2:ℝ)*(z i j:ℝ)| < ((T.period i).val:ℝ) by rwa [abs_mul,abs_of_pos zero_lt_two])
 constructor; · exact_mod_cast ha
 exact_mod_cast hb.le
lemma unitPeriod (T : Itinerary) : Tendsto (fun i=>((T.period i).val:ℝ)) atTop atTop:=by simpa using T.huge 0
private lemma direct (T : Itinerary) (z : Cover) : Tendsto (fun i=>thread (wrap (T.period i) z)) atTop (𝓝 (coverLine z)) := by
 simpa using (shrink (Medium.constant T z)).naked.add (tendsto_const_nhds (x:=coverLine z))
lemma payment (D : List Axis) : ∃ C>0,∀ z : Cover, |derive D coverLine z| * ((diam z+1:ℝ))^(D.length+2) ≤ C:=by
 obtain ⟨C,hC,H⟩:= far D; refine ⟨C,hC,?_⟩
 intro z
 let T:=itinerary (2:Side) (by decide)
 have h := wideDer (Medium.constant T z) D
 have hh : Tendsto (fun i=>derive D thread (wrap (T.period i) z)) atTop (𝓝 (derive D coverLine z)):= by simpa using h.naked.add (tendsto_const_nhds (x:=derive D coverLine z))
 apply le_of_tendsto (hh.abs.mul_const _) ?_
 filter_upwards [(Medium.constant T z).unwrap] with i hi
 specialize H (wrap (T.period i) z); rw [← diam_lift,hi] at H; exact H
lemma Medium.routed {T : Itinerary} {z: ℕ→Cover} {p : E4}(hx:Tendsto (fun i=> incVec (T.gap i) (z i)) atTop (𝓝 p)): Medium T z:=by
 refine ⟨2,?_⟩
 filter_upwards [hx.norm.eventually (gt_mem_nhds (show ‖p‖ < ‖p‖+1 by linarith)),T.cutoff.eventually (gt_mem_nhds (show 0<(‖p‖+2)⁻¹ by positivity)),T.cutoff.eventually (gt_mem_nhds zero_lt_one)] with i hi hg ht
 have hp:= T.positive i
 rw [norm_span _ hp] at hi
 have hb : (T.gap i) * (diam (z i)+1:ℝ) ≤ (‖p‖+2):=by have := mul_le_mul_of_nonneg_left (chart_ge (z i)) hp.le; nlinarith only [this,ht,hi]
 have hh : (‖p‖+2) ≤ (T.gap i)⁻¹:=by simpa using (inv_le_inv₀ (show 0<(‖p‖+2)⁻¹ by positivity) hp).2 hg.le
 apply le_of_mul_le_mul_left (a:= T.gap i) (hb.trans (hh.trans_eq ?_)) hp; rw [zpow_neg,zpow_natCast]; field_simp
lemma offLine (T : Itinerary) (z : ℕ→Cover) (D : List Axis) {p : E4}(hp : p ≠ 0)(hx:Tendsto (fun i=> incVec (T.gap i) (z i)) atTop (𝓝 p)): Tendsto (fun i=> (T.gap i)⁻¹^(D.length+2)*derive D coverLine (z i)) atTop (𝓝 ((casual D p).re)):=by
 have hz:= Medium.routed hx
 let x i:= wrap (T.period i) (z i)
 have hw: Tendsto (fun i=>incVec (T.gap i) (Lattice.lift (x i))) atTop (𝓝 p) := hx.congr' (hz.unwrap.mono (fun i hi=>by simp only [x,hi]))
 have hb: Tendsto (fun i=> (joint (T.gap i) D (x i)).re) atTop (𝓝 (casual D p).re) := Complex.continuous_re.continuousAt.tendsto.comp (joint_casual _ _ _ _ _ hp T.grid_eq T.positive T.clears T.cutoff hw)
 have h := hb.sub (wideDer hz D (D.length+2)); simp_rw [spin, zpow_neg, zpow_natCast, inv_pow,mul_sub,x,sub_sub_cancel,sub_zero] at h ⊢; exact h
lemma nod (z : Cover) : coverLine (-z) = coverLine z := by
 let T:=itinerary (2:Side) (by decide)
 have h:= direct T (-z)
 apply tendsto_nhds_unique h; conv=> arg 1; ext i; rw [map_neg,thread,toroid_even]
 exact direct T z
lemma harmonic_kernel (z : Cover) : (∑ i:Axis,(coverLine (z+step i)+coverLine (z-step i)-2*coverLine z)) = -(if z=0 then 1 else 0):=by
 let T := itinerary (2:Side) (by decide)
 let c (i:ℕ) (w:Cover):= thread (wrap (T.period i) w)
 let b (j:ℕ) (i:Axis) := c j (z+step i)+c j (z-step i)-2*c j z
 have h := tendsto_finsetSum Finset.univ (fun i (_:i∈(Finset.univ:Finset Axis))=> ((direct T (z+step i)).add (direct T (z-step i))).sub (Tendsto.const_mul 2 (direct T z)))
 change Tendsto (fun j=> ∑ i:Axis,b j i) atTop _ at h
 apply tendsto_nhds_unique h
 have he : Tendsto (fun j=> (((T.period j).val:ℝ)^(-4:ℤ))) atTop (𝓝 0):=by
   convert (tendsto_inv_atTop_zero.comp (unitPeriod T)).pow 4 using 1
   · funext j; simp [zpow_neg]; rfl
   simp
 have hv : Tendsto (fun j=> -(if z=0 then 1 else 0)+(((T.period j).val:ℝ)^(-4:ℤ))) atTop (𝓝 (-(if z=0 then 1 else 0))) := by simpa using he.const_add (-(if z=0 then (1:ℝ) else 0))
 apply hv.congr'
 filter_upwards [(Medium.constant T z).unwrap] with i hi
 have h0 : z=0 ↔ wrap (T.period i) z=0:=⟨fun h=>by rw [h,map_zero],fun e=>by rw [←hi, e]; ext a; simp [Lattice.lift]⟩
 simp_rw [b,c,map_add,map_sub,wrap_step,h0]; apply Eq.symm; convert Pert.Orb.lap_shift (wrap (T.period i) z) using 1; simp [Pert.Orb.lap, thread,two_mul,two_smul]
end YM.SchemeRG11.Catch
