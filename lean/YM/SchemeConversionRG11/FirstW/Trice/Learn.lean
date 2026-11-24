import YM.SchemeConversionRG11.FirstW.Trice.Reap
/-! Unique flux along difference sequences permits differentiation via legitimate kernels on punctured space. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function Filter Set MeasureTheory Metric Lattice Pert Align Topology Maxwell Analysis Deck Next.Rank.Radian
open scoped Topology BigOperators Classical
variable {T:Itinerary}{c:ℕ→Side}{G:Gauge}{K:Set E4}{E:Type}[NormedAddCommGroup E] [NormedSpace ℝ E]
variable {v:E4} {f:Hall T E}{F g:E4→E}
omit [NormedSpace ℝ E] in
lemma scouring (hp:Meets T K f F)(hk:v∈K){ε:ℝ}(he:0<ε): ∃ r>0,∀ᶠ i in atTop,∀ z:Site (T.period i),‖out T i z-v‖<r → ‖f i z-F v‖≤ ε := by
 by_contra! h; let p(i:ℕ):=1/((i:ℝ)+1)
 have hv(i:ℕ):∃ j≥i,∃ z:Site (T.period j), ‖out T j z-v‖<p i ∧ ε<‖f j z-F v‖ := frequently_atTop.1 (h (p i) (by unfold p; positivity)) i
 choose n hn z hs ht using hv; let e:=tendsto_atTop_mono (f:=id) hn tendsto_id
 have hl: sails (Rig.path T n e) z v:= by unfold sails; rw [tendsto_iff_dist_tendsto_zero]; refine squeeze_zero (fun _=>dist_nonneg) (fun i=> show _ ≤ p i from (le_of_lt (by rw [dist_eq_norm];exact hs i))) ?_; exact tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x:=1)))
 obtain ⟨i,hi⟩:= ((tendsto_iff_dist_tendsto_zero.1 (hp n e v hk z hl)).eventually (gt_mem_nhds he)).exists; exact not_lt.mpr (le_of_lt (show _< ε from (by rw [←dist_eq_norm]; exact hi))) (ht i)
def axisPath (x:Cover)(a:Axis)(i:ℕ): Cover:= x+i • step a
def tideCnt (T:Itinerary)(s:ℝ)(i:ℕ): ℕ:= ⌊s/T.gap i⌋₊
lemma march (i:ℕ)(j:ℕ)(x:Cover)(a:Axis): Moss T i (axisPath x a j)= Moss T i x+((j:ℝ)*T.gap i) • basis a := by
 rw [axisPath,Moss,Moss,inc_add]; congr 1
 induction j with | zero=> simp; ext l; simp | succ j ih=>simp only [add_smul,Nat.cast_succ,inc_add,ih, one_smul, inc_step]; simp [add_mul,add_smul] -- check
lemma march_norm (s:ℝ)(a:Axis): ‖s • basis a‖=|s|:=by simp [norm_smul,basis]
lemma bulwark (k:ℕ){s:ℝ}(hs:0≤ s): T.gap k*(tideCnt T s k) ≤ s ∧ s-T.gap k≤ T.gap k*(tideCnt T s k) := by
 have h:= T.positive k; have h1 := Nat.floor_le (show 0≤ s/T.gap k from by positivity); have h2:= Nat.lt_floor_add_one (s/T.gap k); unfold tideCnt; rw [le_div_iff₀ h] at h1; rw [div_lt_iff₀ h] at h2; constructor <;> linarith
lemma meeting (h:Meets T K f F)(hp:IsOpen K)(hx:v∈K)(a:Axis)(hv: Meets T K (ray a f) g)(hc:MarkGrid T c){ε:ℝ}(he:0<ε): ∀ᶠ r in 𝓝[>] (0:ℝ), ‖F (v+r • basis a)-F v-r • g v‖ ≤ r*ε := by
 obtain ⟨u,U,hU⟩:= scouring hv hx he; obtain ⟨R,hR,H⟩:= Metric.mem_nhds_iff.mp (hp.mem_nhds hx); let x i:=mark (c i) v; let y i j:= axisPath (x i) a j; have hw:= chart_mark hc v
 filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds (gt_mem_nhds (by linarith : (0:ℝ)<u/2)), eventually_nhdsWithin_of_eventually_nhds (gt_mem_nhds hR)] with s hs hs' hsR
 have h0:0<s:= hs; let d:=tideCnt T s; let t(i:ℕ):=(d i:ℝ)*T.gap i
 have hh:Tendsto t atTop (𝓝 s):=by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g:=fun i=>s-T.gap i) ?_ (tendsto_const_nhds (x:=s)) (fun i=>show s-T.gap i≤t i from ?_) ?_
    · simpa only [sub_zero] using ((tendsto_const_nhds (x:=s)).sub T.cutoff)
    · unfold t d; rw [mul_comm]; exact (bulwark _ hs.le).2 -- hs type
    intro i; unfold t d; rw [mul_comm]; exact (bulwark i h0.le).1
 let Y i j:=wrap (T.period i) (y i j); let q:=v+s • basis a
 have H₁:Tendsto (fun i=> f i (Y i (d i))) atTop (𝓝 (F q)):= h id tendsto_id q (H (mem_ball_iff_norm.mpr (by unfold q; rw [add_sub_cancel_left,march_norm,abs_of_pos h0]; exact hsR))) (fun i=>Y i (d i)) (show sails T (fun i=>Y i (d i)) q from sails_wrap (u:=fun i=>y i (d i)) (show Harbor T (fun i=> y i (d i)) q from by unfold Harbor y; simp_rw [march]; exact hw.add (hh.smul_const _)))
 have H₀:Tendsto (fun i=>f i (Y i 0)) atTop (𝓝 (F v)):= h id tendsto_id v hx (fun i=>Y i 0) (show sails T (fun i=>Y i 0) v from by simp_rw [Y,y,axisPath,zero_smul,add_zero]; exact sails_wrap hw)
 refine le_of_tendsto_of_tendsto (((H₁.sub H₀).sub (hh.smul_const _)).norm) (hh.mul_const ε) ?_ -- prime?
 have heR: ∀ᶠ i in atTop,∀ j:ℕ,j≤d i→ ‖Moss T i (y i j)-v‖< u := by
    filter_upwards [(tendsto_iff_dist_tendsto_zero.mp hw).eventually (gt_mem_nhds (by linarith : (0:ℝ)<u/2))] with i hi j hj
    unfold y; rw [march, add_sub_right_comm]; apply lt_of_le_of_lt (norm_add_le ..); rw [march_norm, abs_of_nonneg (by have h:=T.positive i; positivity)]
    have hz: (j:ℝ)*T.gap i≤ s:=by rw [mul_comm]; exact le_trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hj) (T.positive i).le) (bulwark i h0.le).1
    have hy: ‖Moss T i (x i)-v‖ < u/2:=by rw [←dist_eq_norm]; exact hi
    linarith
 filter_upwards [heR,hU, entryM T (u+‖v‖)] with i hi hU hL
 have he(j:ℕ)(e:j≤d i): ‖out T i (Y i j)-v‖<u:=by
    unfold out; rw [show lift (Y i j)=y i j from hL _ ?_]; exact hi j e
    have hD := norm_sub_norm_le (Moss T i (y i j)) v; unfold Jam; linarith only [hD, hi j e]
 have H(j:ℕ)(hj:j≤d i): ‖f i (Y i j)-f i (Y i 0)- ((j:ℝ)*T.gap i) • g v‖ ≤ ((j:ℝ)*T.gap i)* ε:= by
    induction j with
    | zero=> simp
    | succ j ih=>
      let L:= ray a f i (Y i j); have ht : L=(T.gap i)⁻¹ • (f i (Y i (j+1))-f i (Y i j)):= by
         have e : Y i (j+1)=Y i j+step a:= by simp only [map_add,one_smul,Y,y,axisPath,add_smul,add_assoc,wrap_step]
         simp only [L,ray,surface,combine,up,e,Pi.smul_apply,List.length_singleton,pow_one]
      have hA:= hU (Y i j) (he j (by omega)); have hQ : T.gap i • L= f i (Y i (j+1))- f i (Y i j) := by rw [ht,smul_inv_smul₀ (T.positive i).ne']
      have hz: ‖T.gap i • (L-g v)‖≤ T.gap i*ε := by rw [norm_smul,Real.norm_of_nonneg (T.positive i).le]; exact mul_le_mul_of_nonneg_left hA (T.positive i).le
      simp only [Nat.cast_add,Nat.cast_one, add_mul,one_mul, add_smul]
      refine le_trans (le_of_eq (congrArg norm (show _= (f i (Y i j)-f i (Y i 0)-((j:ℝ)*T.gap i) • g v)+T.gap i • (L-g v) from ?_))) ((norm_add_le ..).trans (add_le_add (ih (by omega)) hz)); rw [smul_sub,hQ]; abel
 exact H _ le_rfl
lemma equity (h:Meets T K f F)(hp:IsOpen K)(hx:v∈K)(a:Axis)(hv: Meets T K (ray a f) g)(hc:MarkGrid T c)(e:DifferentiableAt ℝ F v): g v=grad a F v:= by
 let V(r:ℝ):= v+r • basis a
 let Z(r:ℝ):= r⁻¹ • (F (V r)-F v)
 have h1:Tendsto Z (𝓝[>] 0) (𝓝 (grad a F v)):= by
   have he:HasDerivAt V (basis a) 0:= by simpa only [one_smul] using! (((hasDerivAt_id (0:ℝ)).smul_const (basis a)).const_add v)
   have hv: V 0=v:= by simp [V]
   have H := (show HasFDerivAt F (fderiv ℝ F v) (V 0) from by rw [hv]; exact e.hasFDerivAt).comp_hasDerivAt 0 he
   simpa only [Z,V,Function.comp_def,zero_add,add_zero,zero_smul] using! H.tendsto_slope_zero_right -- check
 have h2:Tendsto Z (𝓝[>] 0) (𝓝 (g v)):= by
   rw [Metric.tendsto_nhds]; intro ε he; filter_upwards [self_mem_nhdsWithin, meeting h hp hx a hv hc (half_pos he)] with i hi H
   have hq:0 < i:=hi; change dist (Z i) (g v)< ε; rw [dist_eq_norm]; unfold Z; rw [show i⁻¹ • (F (V i) - F v) - g v=i⁻¹ • (F (V i)-F v-i • g v) from by rw [smul_sub (i⁻¹) (F (V i) - F v), inv_smul_smul₀ hq.ne'], norm_smul, Real.norm_of_nonneg (by positivity), inv_mul_lt_iff₀ hq]; exact H.trans_lt (mul_lt_mul_of_pos_left (half_lt_self he) hq)
 exact tendsto_nhds_unique h2 h1
lemma matched (h:Meets T K f F)(hp:IsOpen K)(a:Axis)(hv:Pleased T K f)(hc:MarkGrid T c)(e:∀ x∈K,DifferentiableAt ℝ F x): Meets T K (ray a f) (grad a F):=by obtain ⟨Y,H⟩:= hv; exact (H [a]).congr (Eventually.of_forall fun _=>rfl) fun _ hx=> equity h hp hx a (H _) hc (e _ hx)
end YM.RG11.FirstW
