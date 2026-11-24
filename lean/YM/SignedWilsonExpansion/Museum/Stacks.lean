import YM.SignedWilsonExpansion.Museum.Clear
/-! # Full UV then period for ANY such joint TEST, same ordered appointment at all cap spectra. Actual fixed labels. -/
set_option autoImplicit false
noncomputable section
namespace YM.SignedWilsonExpansion.Museum
open FullVolume Function Filter Set MeasureTheory Lattice Wilson RG Extraction Extraction.Lease Difference Gaps Cells Asymptotics Finset
open PhysicalNext.Repeat.Legato
open scoped Topology BigOperators ContDiff Classical
variable {I ι:Type*}{n:ℕ}{G:Gauge}(C:Family G)(f:Test n)(r:ℝ)
local notation "X" => Points n
local notation "Z" => tsupport ( f : X → ℂ )

def addressSite (N p:ℕ) (x:Points n):Ps N p C n:=wrap _ ∘ address (C.S.a N) (r • x)
def gate (N p:ℕ)(u: Ps N p C n): Set (Points n):=(addressSite C r N p) ⁻¹' {u}
def mass (N p:ℕ)(u:Ps N p C n): ℂ:= ∫x in gate C r N p u,f x
private lemma finalGate (N p:ℕ)(u:Ps N p C n): MeasurableSet (gate C r N p u):=by
    have wire : Measurable (address (C.S.a N):Points n→Fin n→ Cover):= measurable_to_countable (fun y=> measurable_segment ( C.S.a_pos N ) (address (C.S.a N) y)) -- check
    let S:Set (Fin n→ Cover):= {x|wrap _ ∘ x=u}
    exact (Set.to_countable S).measurableSet.preimage ( wire.comp (continuous_const_smul r).measurable )
lemma variationP (N p:ℕ): ∑ u:Ps N p C n, ‖mass C f r N p u‖ ≤ ∫ x, ‖f x‖:=by
    have int' : Integrable (fun x=> ‖f x‖):= (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport).norm
    have he (x) : ‖f x‖=∑ u:Ps N p C n,( gate C r N p u ).indicator (fun t=>‖f t‖) x:=by simp [Set.indicator_apply,gate]
    refine le_trans ( b:= ∑u:Ps N p C n,∫ x in gate C r N p u, ‖f x‖ ) (Finset.sum_le_sum fun u _=>norm_integral_le_integral_norm _) ( Eq.le ?_ ); conv_rhs=> rw [show (fun x=>‖f x‖)= (fun x=>∑ u:Ps N p C n, ( gate C r N p u ).indicator (fun t=>‖f t‖) x) from funext he]
    rw [integral_finsetSum _ fun i _=>int'.indicator ( finalGate C r N p i )]; exact Finset.sum_congr rfl fun u _=> (integral_indicator ( finalGate C r N p u )).symm

lemma congress (N p:ℕ)(v:Ps N p C n→ℂ): f.applyTo (v ∘ addressSite C r N p)= ∑ u: Ps N p C n,mass C f r N p u*v u ∧ Integrable (fun x=> f x*(v ∘ addressSite C r N p) x):=by
   have he : (fun x=> f x*(v ∘ addressSite C r N p) x)=(fun x=>∑ i:Ps N p C n,(gate C r N p i).indicator (fun x=>f x*v i) x):=funext fun x=> by simp [indicator_apply,gate]
   have hn (i:Ps N p C n) : Integrable ((gate C r N p i).indicator (fun x=>f x*v i)) := (( f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport ).mul_const _).indicator (finalGate ..)
   unfold Test.applyTo; rw [he,integral_finsetSum _ fun i _=> hn i]; exact ⟨Finset.sum_congr rfl fun i _=> ((integral_indicator ( μ:=volume ) ( finalGate C r N p i )).trans ( integral_mul_const .. )),integrable_finsetSum _ fun i _=> hn i⟩

variable (φ:(I→ℂ)→ℂ)(m:I→Fin n→ C.book.Token)
abbrev request (N p:ℕ):Ps N p C n→ℂ:= fun u=>φ fun j=> C.numeric N p (m j) u
abbrev cafe (N p:ℕ)(x:X):ℂ:=φ fun j=> genuine C (m j) r N p x
abbrev summit (N p:ℕ): ℂ := ∑ u:Ps N p C n,mass C f r N p u*request C φ m N p u
lemma valued (N p:ℕ): f.applyTo (cafe C r φ m N p)=summit C f r φ m N p ∧ Integrable (fun x=> f x*(cafe C r φ m N p) x):=congress C f r N p (request C φ m N p)
variable {C} {L:Filter ι} {T: (Points n) →ℂ} {Y:Set  (Points n) }
lemma pay (s:IsOpen Y) (h:Z ⊆ Y) (q:ContinuousOn T Y): Integrable (fun x=> f x*T x) :=by
   refine Continuous.integrable_of_hasCompactSupport ?_ ( HasCompactSupport.mul_right f.hasCompactSupport (f':=T) )
   refine continuous_iff_continuousAt.mpr fun x=>?_ ; by_cases ht : x∈ Y
   · exact f.continuous.continuousAt.mul ((q x ht).continuousAt (s.mem_nhds ht))
   refine continuousAt_const.congr (?_ : (fun _=> (0:ℂ)) =ᶠ[𝓝 x] fun a=> f a*T a)
   filter_upwards [isOpen_compl_iff.mpr (isClosed_tsupport _) |>.mem_nhds (show x∈ Zᶜ from fun t=> ht (h t))] with i hi; simp [image_eq_zero_of_notMem_tsupport hi]
lemma billing {A:ι→X→ℂ}(w:TendstoUniformlyOn A T L Z) (h:∀ᶠ i in L, Integrable (fun x=> f x*A i x)) (t:Integrable (fun x=> f x*T x)): Tendsto ( fun i=> f.applyTo (A i) ) L (𝓝 (f.applyTo T)):=by
   let C':ℝ:=∫ x, ‖f x‖
   have hm:0≤ C':= integral_nonneg fun _=>by positivity
   apply Metric.tendsto_nhds.mpr; intro ε ep; let E:=ε/(1+C'); have hE:0 < E:= div_pos ep (by linarith); filter_upwards [Metric.tendstoUniformlyOn_iff.mp w E hE,h] with i hi hp
   rw [dist_eq_norm,Test.applyTo,Test.applyTo,←integral_sub hp t]
   have hS(x:Points n): ‖( f x*A i x )-f x*T x‖ ≤ ‖f x‖*E:=by
      by_cases H:x∈ Z; · rw [← mul_sub,norm_mul]; exact mul_le_mul_of_nonneg_left ((dist_eq_norm ..).symm.trans_le (( dist_comm .. ).trans_le ( hi x H ).le )) (norm_nonneg _)
      simp [image_eq_zero_of_notMem_tsupport H]
   have hh:= norm_integral_le_of_norm_le (μ:=volume) (f:=fun x=> f x*A i x - f x*T x) (( f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport ).norm.mul_const E) (Eventually.of_forall hS); rw [integral_mul_const] at hh; refine hh.trans_lt (lt_of_lt_of_le (b:=(1+C')*E) ( mul_lt_mul_of_pos_right (show C'<1+C' by linarith) hE ) ( Eq.le ?_ )); unfold E; field_simp
section period
variable (hφ:Continuous φ)
include hφ
lemma interim_pay (hv:PositionsUV C Extraction.Sequence.full)(p:ℕ)(h:Prism C.S Z p r): Integrable (fun x=> f x*φ fun j=>amid (p:=p) hv (m j) ( r • x )):=
    pay f ((nohitOpen C.S p n).preimage (continuous_const_smul r)) h ( hφ.comp_continuousOn (continuousOn_pi.mpr fun i=> (wawa hv (m i)).1.comp ( continuous_const_smul r ).continuousOn fun _ hu=> hu) )
lemma UV_test (hv:PositionsUV C Extraction.Sequence.full)(p:ℕ)(h:Prism C.S Z p r): Tendsto (fun N=> summit C f r φ m N p) atTop (𝓝 (f.applyTo fun x=> φ fun j=> amid (p:=p) hv (m j) (r • x))) :=
   (billing f (interimUniform Z r φ f.hasCompactSupport hv m hφ h) (Eventually.of_forall fun i=> (valued C f r φ m i p).2) (interim_pay f r φ m hφ hv p h)).congr (fun N=> (valued C f r φ m N p).1)
variable (R:Run G) {o:Extraction.Order}(h:G.Simple) (hv:PositionsUV R.family Extraction.Sequence.full) {S:Table R.family.book} (hs:S.Smooth) (hX:(Homes.track o).PointLimits R.family S) (q:I→Fin n→ R.family.book.Token) (hr:0 < r)
include hs h hX hr hv
lemma sequenceP : (Homes.track o).limits (fun p=>Prism R.family.S Z p r) (summit R.family f r φ q) (f.applyTo fun x=> φ fun j=> S.read (r • x) (q j)) :=by
   have w:= o.per.cofinal.eventually (eligible Z r f.hasCompactSupport R.family.S f.tsupport_subset hr)
   refine ⟨w,fun p=>f.applyTo fun x=> φ fun j=> amid (p:=p) hv (q j) (r • x),fun i t=> UV_test f r φ q hφ hv i t,billing f ?_ ?_ ?_⟩
   exacts [ periodUniform Z r φ f.hasCompactSupport R h hv hs hX q hφ hr f.tsupport_subset, w.mono fun i hi=> interim_pay f r φ q hφ hv _ hi, f.smearing ( hφ.comp_continuousOn ( continuousOn_pi.mpr fun i=> ( S.smooth_read hs (q i) ).continuousOn.comp (continuous_const_smul r).continuousOn fun _ t=> Work.A05.smul_conf hr t ) ) ]
end period
end YM.SignedWilsonExpansion.Museum
