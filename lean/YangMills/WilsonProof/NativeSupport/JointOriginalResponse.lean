import YangMills.WilsonProof.NativeSupport.JointOriginalHistory
import YangMills.WilsonProof.NativeSupport.JointMicroResponse

/-! A uniform susceptibility for the actual calibrated traversal, under its
interpolated nonlinear law at the frozen field, including any physical
generating subset at independently placed sites. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 170000
noncomputable section
namespace YM.Integration.InletSusceptibility.Dated
open Function Finset Filter Lattice RG Wilson Marker MergeProof MergeProof.Accent MeasureTheory RGGapR2
open RGComparison.Core16 YM.Pressure Push.BetaTransport PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Pert.Asymptotics WilsonUniformUnmarkedInletEnergySites WilsonUniformUnmarkedInletBondRemainder
open WilsonUniformUnmarkedInletConnectedShift Packet JointShadow JointMoments
open scoped Classical BigOperators Topology
variable {G:Gauge} {I:Type} [Fintype I] [DecidableEq I] [Nonempty I] {R:Run G} {C:Campaign R}
variable {Θ:Luna.Tableau C.width 300} {v:ℕ→ℕ→ℝ}
local notation "A₀" => R.alloy.B.a

theorem original_response (sky:Campaign.Sky R C Θ v) (simple:G.Simple)
    (slow:∀ n,(((A₀).S.block n).val:ℝ) ≤ Real.log (2+Real.log ((A₀).clock.hatBeta n)))
    (blocks:∀ j,3 ≤ ((A₀).S.block j).val)
    (support:∀ j,(((A₀).budget j).supportExponent+1)*((((A₀).S.block (j-1)).val:ℝ)^4) ≤ Real.sqrt ((A₀).clock.hatBeta j))
    (radius W:ℕ) :
    let s:ℕ:=(2*radius+1)^4
    let d₀:=radiusDegree W s (tariffDegree Θ.price)
    ∀ᶠ k:ℕ in atTop,∀ t N,k ≤ t → ∀ tn:t < N,
      ((N-t:ℕ):ℝ)*Real.log 3 ≤ R.family.S.scale N-R.family.S.scale t →
      R.family.S.scale N-R.family.S.scale t ≤ (W:ℝ)*Real.log ((A₀).clock.hatBeta N) →
      ∀ per (T:Slices A₀ per) (loc:I → Site ((A₀).S.side N per)) (F:I → Config G ((A₀).S.side N per) → ℝ),
        (∀ i,LocalOn (halo radius {loc i}) (F i)) → (∀ i,GaugeInvariant (F i)) →
        (∀ i,Continuous (F i)) → (∀ i X,|F i X| ≤ 1) →
        ∀ (p:ℕ) (β δ:ℕ→ℝ) (r:ℝ),2*(2*d₀+1) ≤ p →
          let d:=traversal T tn.le
          let B:=line R.family.path per t N
          let Y:=temperatures β δ r
          let g:=regulatorRun R.family N per N
          let x:ℝ:=height R N
          let h:=((x^d₀)⁻¹)^2
          Y d.depth=B d.depth →
          (∀ i,0 < i → i < d.depth → |Y i-B i| ≤ g^p) →
          0 < h ∧ x ≤ 4/g^2 ∧ ∀ E:Finset I,h*(∑ q∈interior d,|picture d β δ 1 (micro F E h) r q|) ≤ (3/2:ℝ)^E.card := by
  intro s d₀
  let c:=max 1 ((A₀).clock.kernel.penalty*2)
  have cp:1 ≤ c:=le_max_left ..
  filter_upwards [inlet_admission R simple (Fintype.card I) W s (tariffDegree Θ.price) c cp] with k funded
  intro t N kt tn lower upper per T loc F localF sym ct unit p β δ r trunc d B Y g x h endY near
  obtain ⟨heat,hC,mC,stain,thermal⟩:=funded t N kt tn.le upper
  obtain ⟨_,_,band,push⟩:=thermal per p trunc
  obtain ⟨_,_,sc,tm,_⟩:=calendar_expenses R simple T tn.le W support lower upper
  have days:((N-t:ℕ):ℝ) ≤ (W:ℝ)*x:=by dsimp only [x];exact_mod_cast tm
  have span:(scale d:ℝ) ≤ x^W:=by dsimp only [x,d];exact_mod_cast sc
  have width:2*(W:ℝ) ≤ x:=by linarith only [mC,(Nat.cast_nonneg (Fintype.card I):0 ≤ (Fintype.card I:ℝ)),(Nat.cast_nonneg W:0 ≤ (W:ℝ))]
  obtain ⟨_,ur,small⟩:=paid_calendar T tn.le W s (tariffDegree Θ.price) heat width days span
  have hp:0 < h:=sq_pos_of_pos (inv_pos.mpr (pow_pos (show 0 < x by linarith only [heat]) _))
  refine ⟨hp,band,?_⟩
  intro E
  let sig (q:sites ((A₀).S.side N per) d):ℝ:=if 0 ≤ picture d β δ 1 (micro F E h) r q then 1 else -1
  have paid (i:ℕ) (pos:0 < i) (ins:i < d.depth):2*(|Y i-B i| *c) ≤ h:=by
    apply le_trans _ push
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (near i pos ins) (zero_le_one.trans cp)) zero_le_two
  have signs (q):|sig q| ≤ 1:=by dsimp only [sig];split <;> norm_num
  have cap (i:ℕ):linkCap ((A₀).clock.op i per) ≤ c:=le_max_right ..
  obtain ⟨O,D,ok,re,_,read⟩:=history sky simple slow blocks T tn.le loc F radius W c cp cap localF sym ct unit
    heat hC mC days span stain t tn.le le_rfl (fun i=>Y i-B i) sig paid signs
  let Rt:=R.T.history N per t
  let old:=ready (I:=I) (n:=(A₀).S.side N per) (t:=t) (N:=N) t
  have masked:=(clip_ledger Rt (place T loc tn.le) O D old ok).1
  obtain ⟨quiet,out,root⟩:=frozen_outlet Rt (place T loc tn.le) (clip old O) (clip old D)
    (R.T.choice.represents N per t tn.le).good.labels masked (clip_root old re)
  let H:=∑ X,clip old O X (1:Config G ((A₀).S.side t per))
  have live (i:Names I t N ((A₀).S.side N per)):=((root i).trans (ur t le_rfl tn.le)).trans small
  refine response d (traversal_ok T tn.le) B β δ r 1 E F ct sym h hp.le H quiet (fun i=>by
    apply le_trans _ (live i);apply le_of_eq
    apply sum_congr (by ext S;simp)
    intro S _;rfl)
    (Real.exp (Rt.exponent 1)) (Real.exp_pos _) ?_
  intro A z
  have matched:=read A z (1:Config G ((A₀).S.side t per))
  rw [exposed,dif_neg tn.ne,Complex.ofReal_one,one_mul] at matched
  have closed:recorded Rt old O D 1=(Real.exp (Rt.exponent 1):ℂ) • Poly.pass H:=out
  rw [closed,open_scalar] at matched
  have cf:Continuous (micro F A h):=continuous_finsetProd _ (fun i _=>continuous_const.add (continuous_const.mul (ct i)))
  have gf:GaugeInvariant (micro F A h):=by
    intro b X;unfold micro;exact prod_congr rfl fun i _=>by rw [sym i b X]
  exact matched.trans (law_moments d (traversal_ok T tn.le) B Y endY cf gf sig h z 1)

end YM.Integration.InletSusceptibility.Dated
