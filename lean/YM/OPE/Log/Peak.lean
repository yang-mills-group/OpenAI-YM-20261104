import YM.OPE.Log.Snap
import YM.OPE.Log.Port
/-! # Polynomial-log compensation from measurements at one radius -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log
open Function Filter Set Metric Lattice RG Polar
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(U:Spec.Final C f S) {I J L : Type}[Fintype I][DecidableEq I][Fintype J]
    {l:Filter L}[l.NeBot] {r:L→ℝ}(hr:Tendsto r l (𝓝[>] 0)) (p:I→ C.book.Token)
    {𝓕:Filter (ℕ×ℕ)}[𝓕.NeBot] {W r' D} (L': LogPackage C W r' D)(hG:G.Simple) (hF:𝓕 ≤ f.fuse)(h:MatrixTicket (C:=C) S U.sector.derivatives 𝓕)
    {P:Prescription U.sector.derivatives}(w:Mode U.sector.derivatives)(hP:P.Coherent)
    (p₀:I)
    {X:L→ I→ E4}{η M : ℝ} (hη:0<η)
set_option quotPrecheck false
local notation "T"=> (fun i=>run (r i))
local notation "V"=> (fun i=>r i^sigma p/r i^w.fst)
local notation "F"=> (fun i (x:I→ E4)=> (V i :ℝ) • P.ope w (centered X r i x) p 0)
include hr hη p₀
lemma surveys (hX:∀ᶠ i in l, WithinRoom (r i) M η (X i) 0) : ∀ᶠ i in l,∀ x∈ closedBall (0:I→E4) 1, Watches (f:=F i) x (run (r i)^2) (2*((Fintype.card (I×Axis):ℝ)+1)):=by
    let z:= V; let T':= T; let K a i:= Real.exp (a*T' i); let a:= (-(sigma p :ℝ) + w.fst)+1; have hv:=loglife hr; have hT:=run_towards hr; have hh:RateIs l T' z (a-1):=((hv.power (sigma p)).div (hv.power w.fst)).swap (by unfold a; ring)
    have hz:=eventually_all.mpr (fun i=> eventually_all.mpr fun s=> turnways U (P:=P) p w i s hr hη hX)
    filter_upwards [(hh.pays hT) a (sub_lt_self a one_pos), within_centered hr hη hX,frames_safe (I:=I) (M:=M+η) hr (P.sheet w).support (half_pos hη), hz, hT.eventually_ge_atTop (4*a),hT.eventually_ge_atTop 0,(loglife hr).pos] with i hv ht hx hz hT hu hr x hX
    have hξ:= mem_closedBall_zero_iff.mp hX; let Z:= centered X r i x;
    have he (p:I) (v:Axis) :∃ q, ‖(forwards q).val-basis v‖<knobSize I ∧ Radiates (F i) x (ray p q) (Real.exp (T' i^2)):=by
       obtain ⟨q,hq,hh⟩:= hz v p x hξ; refine ⟨q,hq,(hh.smulReal (z i)).mono ?_⟩; apply (mul_le_mul_of_nonneg_right hv (Real.exp_nonneg _)).trans; rw [← Real.exp_add]; unfold T'; apply Real.exp_monotone; nlinarith only [mul_le_mul_of_nonneg_left hT hu]
    obtain ⟨q,hA,hD⟩:= he p₀ timeAxis; apply knobs_cost _ _ hD.at_center _ he
    have hi: ContDiffAt ℝ ∞ (fun t:(I→E4)×E4=> P.ope w t.1 p t.2) (Z,0):= smooth_ope P U.room.kernel p w (fun u hu=> by rw [show OPE.away (I:=I) Z 0= centered X r i x from (by change OPE.away Z _=Z; unfold OPE.away; simp)]; exact (hx _ (ht x hξ) u hu|>.coin (by positivity))) -- adjust args
    exact ( ( (hi.differentiableAt (by simp)).comp (f:=fun t=> (centered X r i t,(0:E4))) x (by unfold centered; fun_prop)).const_smul (z i)) -- epsilon defeq

include L' hG hF h hP
lemma interpolated (hT: Org.Grill C f)(hX:∀ᶠ i in l,WithinRoom (r i) M η (X i) 0)(hM:0≤M): Wallet l T (fun i=> V i • P.ope w (X i) p 0):=by
    let K:ℝ:= 2*((Fintype.card (I×Axis):ℝ)+1); have hK:1 ≤ K:= by unfold K; have hx:= Nat.cast_nonneg (α:=ℝ) (Fintype.card (I×Axis)); linarith only [hx]
    have hT':=run_towards hr; obtain ⟨m,j,hm,hj,hz,hM',hρ⟩:= enough_spans L' hG hr; obtain ⟨k,hk⟩:= found hT' C.path.levels.fits.mesh (by norm_num: (0:ℝ) ≤ 1/2)
    let g := (fun i (z:I→ E4)=> (r i^sigma p/r i^w.1:ℝ) • P.ope w (centered X r i z) p 0); have hg: Wallet l T (fun i=> g i 0):=by
       apply price_mesh («F»:=g) hT' ((hT'.eventually_ge_atTop 1).mono fun i hi=> one_le_pow₀ hi) (Eventually.of_forall fun i=> hK) (surveys U hr p w p₀ hη hX); intro x hx; obtain ⟨y,P₀,hP₀,h0⟩:= snap hr hK (hz.mono fun i hi=> hi.2.2) X x hx
       have hϕ : ∀ᶠ i in l, WithinRoom (r i) (M+η) (η/2) (C.S.gridPoint (j i) ∘ P₀ i) 0:=by
          filter_upwards [within_centered hr hη hX,h0] with i hi ht; rw [← ht.2.2]; exact hi _ ht.2.1
       let X' (i):= C.S.gridPoint (j i) ∘ P₀ i; obtain ⟨h',he⟩:= room_regime hr (add_nonneg hM hη.le) (half_pos hη) hϕ; have hD:=subPlot hG hr (half_pos hη) hk hm hj hz hϕ; have hh:= grid_ticket U hT' hP L' hG p₀ p h hm hk hj (by norm_num) (by norm_num) (hz.mono fun i hi=> hi.2.1) (by
          apply (hM'.div hρ).congr; filter_upwards [(loglife hr).pos] with i hi; have hp:= C.S.a_pos (m i); have he:= C.S.a_pos (j i); field_simp) hD (by unfold enveloped OPE.away at h'; simpa only [sub_zero] using! h') he (Eventually.of_forall hP₀) hF hT w
       refine ⟨y,(((hρ.pow hT' (sigma p)).div (hM'.pow hT' w.1)).up.smul hh).congr ?_,h0.mono fun i hi=>hi.1⟩; filter_upwards [(loglife hr).pos,h0] with i hi hq; unfold g; rw [hq.2.2,smul_smul]; congr 1; have hp:=C.S.a_pos (m i); have hh:=C.S.a_pos (j i); simp only [div_pow]; field_simp
    apply hg.congr; filter_upwards with i; simp [g,centered]
end YM.OPE.Log
