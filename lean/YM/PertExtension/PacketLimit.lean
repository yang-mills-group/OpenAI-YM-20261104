import YM.PertExtension.NativeIntegral

/-! Riemann sampling for the infinite Wilson top-cover curl symbol, unrelated to
replacing the bare Wilson action by a cell rule. Used for the self pairing to compare
at exactly the same kinetic normalization. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace YM.PertExtension.LatticePT
namespace Converter
open MeasureTheory Filter Topology Analysis Maxwell Asymptotics Next.Rank Next.Rank.Radian Set Real Metric Lattice Beamer CellsInt Wall Band
open Configuration Air Orb Orbit GaussianScore Function Finset Projection
open scoped ContDiff Topology BigOperators Classical NNReal ENNReal
local notation "ℑ" => Complex.I

variable (p s:RG.Slot)
variable {q : ℕ+}(hq:1<q.val)
def port (n:Side)(z:E4):=addr n (mark n z)
include hq
lemma port_at (z) : Tendsto (fun t=>port (side q t) z) atTop (𝓝 z):= by
  apply (Metric.tendsto_nhds.mpr (fun ε hε => ?_))
  have hp:= (show ∀ᶠ t in atTop, dist (port (side q t) z) z ≤ 4*((side q t).val:ℝ)⁻¹ from Eventually.of_forall fun t=> rock ..)
  have hI:Tendsto (fun t=>((side q t).val:ℝ)⁻¹) atTop (𝓝 0):=by simpa [one_div] using side_rate hq 0
  have hv := squeeze_zero' (Eventually.of_forall fun _=>dist_nonneg) hp (by convert hI.const_mul 4 using 2; exact (mul_zero _).symm)
  exact hv.eventually (gt_mem_nhds hε)

omit hq
@[fun_prop] lemma packet_meas : Measurable (packet p s):= by
    have hm:Measurable pointAt:= rawAxis.measurable.comp (Continuous.smul (g:=id (α:=E4)) (continuous_const (y:=radius)) continuous_id).measurable
    exact ((bubble_meas p s).comp hm).indicator (by
       change MeasurableSet (rawAxis ⁻¹' {x:Momentum|∀ i,x i∈Set.Ioc (-1/2) (1/2:ℝ)}) -- patch
       have hs: {x:Momentum|∀ i,x i∈ Set.Ioc (-(1:ℝ)/2) (1/2)}= Set.pi Set.univ (fun i=> Set.Ioc (-1/2:ℝ) (1/2)):=by ext x;simp
       rw [hs];exact rawAxis.measurable (MeasurableSet.pi Set.countable_univ fun i _=>measurableSet_Ioc))
@[fun_prop] lemma port_meas (n:Side): Measurable (port n):=(show Measurable (addr n) from by exact measurable_of_countable (addr n)).comp (measurable_pi_lambda _ (fun i:Axis=>Int.measurable_ceil.comp ((rawAxis.measurable.eval (a:=i)).div_const (sizeInv n))) : Measurable (mark n)) -- wrong

lemma point_inc z i : (Band.increment i z)=LatticePT.increment i (pointAt z):=by
   rw [Band.increment, Next.Rank.Radian.readD, Pi.sub_apply, Next.Rank.Radian.terrel, congr_fun (Next.Rank.Radian.chore i) z, LatticePT.increment]
   congr 2
   unfold Next.Rank.Radian.chirp
   change (2*π*ℑ * ((z i:ℝ):ℂ))= Complex.I * ((radius*z i:ℝ):ℂ)
   unfold radius;push_cast;ring
lemma unchanged_mass z : mass (pointAt z)=Band.location z:=by unfold mass Band.location; simp_rw [point_inc]
lemma active {x:E4}(hx : x ∈ closedunit)(hp:x≠0) : 0<mass (pointAt x):= by
    have h k: |polarPoint ((1:ℝ),x) k|≤3/4:= by simp_rw [polarPoint,one_smul];rw [abs_le]; obtain ⟨hl,hu⟩:= hx k; constructor <;> linarith
    have hb := location_at (1,x)
    change location ((1:ℝ) • x)=1^2*masswell (1,x) at hb;rw [one_smul,one_pow,one_mul] at hb
    rw [unchanged_mass,hb];exact mass_near hp h
private lemma opencube_open : IsOpen opencube:= by
    have h : opencube = rawAxis ⁻¹' Set.pi Set.univ (fun i: Axis=>Ioo (-1/2:ℝ) (1/2)):=by ext x;simp only [opencube,Set.mem_setOf_eq,Set.mem_preimage,Set.mem_pi,Set.mem_Ioo]; simp only [Set.mem_univ,forall_const];exact Iff.rfl
    rw [h];exact (isOpen_set_pi Set.finite_univ (fun i hi=>isOpen_Ioo)).preimage ((PiLp.homeomorph 2 _).continuous)
private lemma closedunit_closed : IsClosed closedunit:= by
    have h : closedunit = rawAxis ⁻¹' Set.pi Set.univ (fun i: Axis=>Set.Icc (-1/2:ℝ) (1/2)):=by ext x;simp only [closedunit,Set.mem_setOf_eq,Set.mem_preimage,Set.mem_pi,Set.mem_Icc]; simp only [Set.mem_univ,forall_const];exact Iff.rfl
    rw [h];exact (isClosed_set_pi (fun i hi=>isClosed_Icc)).preimage ((PiLp.homeomorph 2 _).continuous)
lemma toward_inside {x:E4} (hr:x∈opencube ∨ x∉closedunit) (hn:x≠0) : ContinuousAt (packet p s) x := by
   rcases hr with hx|hx
   · have hs:= opencube_open.mem_nhds hx
     have he : ∀ x∈opencube,unitbox.indicator _ x=_:=fun x hx=>indicator_of_mem (show x∈unitbox from fun i=>⟨(hx i).1,(hx i).2.le⟩) (fun z=> bubble p s (pointAt z))
     have hE: ContinuousAt (fun z=>bubble p s (pointAt z)) x:= by
         have hM:= (active (fun i=>⟨(hx i).1.le,(hx i).2.le⟩) hn).ne'
         have hg: ContinuousAt (bubble p s) (pointAt x):=by
            unfold bubble;refine ContinuousAt.div ((continuous_finsetSum _ ?_).continuousAt) mass_cont.continuousAt hM
            intro i hi; exact Complex.continuous_re.comp (((LatticePT.phase_cont p).mul (phase_cont s).star).mul ((impulse_cont p i).mul (impulse_cont s i).star))
         exact ContinuousAt.comp hg ((PiLp.homeomorph 2 (fun _:Axis=>ℝ)).continuous.continuousAt.comp (Continuous.smul (g:=id (α:=E4)) (continuous_const (y:=radius)) continuous_id).continuousAt) -- parsing
     exact hE.congr (Filter.mem_of_superset hs fun x hx=> (he x hx).symm)
   have hs := closedunit_closed.isOpen_compl.mem_nhds hx -- hx type
   refine (continuousAt_const (y:=0)).congr <| Filter.mem_of_superset hs fun i hi=>?_
   exact Eq.symm (indicator_of_notMem (by change i∉unitbox; intro hp; exact hi (fun j=>⟨(hp j).1.le,(hp j).2⟩)) _ : packet p s i=0)

lemma shore :∀ᵐ z:E4,(z∈opencube ∨ z∉closedunit)∧z≠0:=by
  filter_upwards [MeasureTheory.ae_all_iff.mpr (fun i:Axis => not_hyperplane i (-1/2)),MeasureTheory.ae_all_iff.mpr (fun i:Axis => not_hyperplane i (1/2)),lit_ae] with z hz ht hn
  apply And.intro _ hn;by_cases h:z∈closedunit
  · exact Or.inl fun i=>by obtain ⟨hl,hu⟩:=h i; exact ⟨hl.lt_of_ne (Ne.symm (hz i)),hu.lt_of_ne (ht i)⟩
  exact Or.inr h
lemma point_cover {x:E4} (h:x∈unitbox): ‖x‖≤1:= by
    rw [← sq_le_sq₀ (norm_nonneg _) zero_le_one,EuclideanSpace.real_norm_sq_eq]
    refine (sum_le_sum (g:=fun (_:Axis)=>(1/2:ℝ)^2) (fun i (_:i∈Finset.univ)=>?_)).trans (le_of_eq ?_)
    · obtain ⟨h₁,h₂⟩:=h i;nlinarith
    simp only [Finset.sum_const,nsmul_eq_mul, Finset.card_univ, Fintype.card_fin, Axis];norm_num

include hq
lemma port_eventually (n:Side)(x:E4): ‖port n x-x‖ ≤ 4:= (by simpa [port,dist_eq_norm] using (show dist (port n x) x ≤ 4*((n.val:ℝ))⁻¹ from rock ..).trans (show _≤_ from by have :=sizeInv_le n;unfold sizeInv at this; linarith only [this]))
lemma limit_packet : Tendsto (fun t=>∫ z:E4, packet p s (port (side q t) z)) atTop (𝓝 (kernelEntry p s)):=by
   let f(t):=(packet p s ∘ port (side q t))
   let S:=Metric.closedBall (0:E4) 5
   let K:E4→ℝ:= S.indicator (fun _=>16)
   have hv : Tendsto (fun t=>∫ z:E4,f t z) atTop (𝓝 (∫ z:E4,packet p s z)):=MeasureTheory.tendsto_integral_filter_of_dominated_convergence K ?_ ?_ ?_ ?_
   exact convert_int p s ▸ hv
   · exact Eventually.of_forall fun t=>(packet_meas p s).aestronglyMeasurable.comp_measurable (port_meas _)
   · filter_upwards with n
     apply Eventually.of_forall fun z=>?_
     have hx:=port_eventually hq (side q n) z
     let x:=port (side q n) z
     change ‖unitbox.indicator (fun z=>bubble p s (pointAt z)) x‖ ≤ K z
     by_cases h:x∈unitbox
     · have hv:= le_trans (show ‖z‖-‖x‖≤ ‖x-z‖ from (norm_sub_norm_le z x).trans_eq (norm_sub_rev ..)) hx
       rw [indicator_of_mem h, show K z=16 from indicator_of_mem (show z∈S from Metric.mem_closedBall.mpr (by unfold x at *;rw [dist_zero_right]; linarith [point_cover h])) ..]
       exact bubble_bound p s (pointAt x)
     rw [indicator_of_notMem h,norm_zero]
     exact Set.indicator_nonneg (fun (_:E4) _=> by positivity) z
   · unfold K S
     rw [integrable_indicator_iff isClosed_closedBall.measurableSet]
     exact integrableOn_const (hs:= (isCompact_closedBall _ _).measure_lt_top.ne)
   exact (shore.mono fun x hx=>(toward_inside p s hx.1 hx.2).tendsto.comp (port_at hq _))
end Converter
end YM.PertExtension.LatticePT
