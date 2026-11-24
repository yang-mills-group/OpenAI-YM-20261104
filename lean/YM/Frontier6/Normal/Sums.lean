import YM.Frontier6.Normal.Cascade

/-! Absolute estimates for summing the tested punctured kernels in full normal
variables. Works for arbitrary arity and Banach target. Does not use positivity,
and shell hypothesis is on the *inductively extended punctured distribution*.
Shell normalization here charged with σ = degree + measure power. Thus if the
hypothesis is a density bound on normalized tests remember to add measure power!
We use upper patch scale ≤1 where needed for the full contour; given fixed s in
local constructions r_patch might be much smaller. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Normal
open Function Filter Set MeasureTheory Metric
open scoped Topology ContDiff BigOperators Classical
variable {X Y:Type*}[NormedAddCommGroup X][InnerProductSpace ℝ X][FiniteDimensional ℝ X][NormedAddCommGroup Y]

def Piece (s:ℝ): Full X→ₗ[ℂ] Full X where
 toFun f:= join (strip X s) f
 map_add' f g:= TestFunction.ext (fun x=> by simp [mul_add]) -- expected definitional confusion
 map_smul' c f:= TestFunction.ext (fun x=> by simp [mul_left_comm])
lemma piece_fits {s t:ℝ} {f:Full X}(h:Fits t f): Fits t (Piece s f):=(join_right ..).trans h
lemma piece_ring {s:ℝ}(h:0<s)(f:Full X): tsupport (Piece s f)⊆Ringed X s:= (join_left ..).trans (strip_ring h)
lemma piece_too_high {s t:ℝ} (h:0<s){f:Full X}(he:Fits t f)(hx: t < s/2): Piece s f=0:= by
   ext1 x; change _ = (0:ℂ); apply image_eq_zero_of_notMem_tsupport; intro hc; exact (not_lt_of_ge (le_trans (show s/2 ≤ ‖x‖ from (piece_ring h f hc).1) (mem_closedBall_zero_iff.mp (piece_fits he hc)))) hx
lemma piece_budget (j:ℕ) : ∃ C:ℝ,0 ≤ C ∧ ∀ (s P:ℝ),0<s→0≤P→∀ (f:Full X),Estimate j s f (Ringed X s) P→ Charge j s (Piece s f:X→ℂ) (C*P):=by
    obtain ⟨A,hA,H⟩:=strip_charge (X:=X) j
    refine ⟨2^j*A, by positivity,fun s P hs hP f hf=> Estimate.due (Estimate.mul (Estimate.subset (H s hs) (subset_univ (Ringed X s))) hf hA hP hs.le (strip X s).contDiff f.contDiff) (piece_ring hs f) (by positivity)⟩

def RingPrices (j:ℕ) (σ r:ℝ) (F:Full X → Y)(P:ℝ):Prop:=0≤P ∧ ∀ (s C:ℝ),0<s→s ≤ 1 →∀ (f:Full X),Fits r f → tsupport f⊆Ringed X s→ Charge j s (f:X→ℂ) C →
    ‖F f‖ ≤ P*C*s^σ

/- Price assumption through pitch shells up to 1. If only know it
through smaller Δ, still infer for our use when 2*r≤Δ: beyond it
only zero tests fit both! -/
lemma RingPrices.shrunk {j:ℕ}{σ r t P:ℝ}{F:Full X→Y} (h:0 ≤ P)(ht:2*r≤t)(hz:F 0=0)(he: ∀ (s C:ℝ),0<s→s ≤ t→∀ (f:Full X), Fits r f→ tsupport f ⊆ Ringed X s→ Charge j s (f:X→ℂ) C → ‖F f‖ ≤ P*C*s^σ) : RingPrices j σ r F P:=by
    refine ⟨h,fun s C hs hs' f hf hh hc=>?_⟩; by_cases g:s ≤ t; · exact he s C hs g f hf hh hc
    have hv : f=0:=by
       refine TestFunction.ext fun x=> by_contra fun hi=>?_; have hp:x∈ tsupport f:= subset_closure hi
       linarith only [(show s/2 ≤ ‖x‖ from (hh hp).1), mem_closedBall_zero_iff.mp (hf hp),ht,lt_of_not_ge g]
    rw [hv,hz,norm_zero]; exact mul_nonneg (mul_nonneg h hc.nonneg) (Real.rpow_nonneg hs.le _)
lemma RingPrices.limits {j:ℕ}{σ r b Q:ℝ}{F:Full X→ Y}(h:RingPrices j σ r F Q)(he:b ≤ r):RingPrices j σ b F Q:= ⟨h.1,fun s B hs hs' f hf=> h.2 s B hs hs' f (hf.up he)⟩

def based (F:Full X→Y)(f:Full X)(i:ℕ):= F (Piece (pitch i) f)
def over (F:Full X→ Y)(f:Full X) := ∑' i:ℕ, based F f i

lemma Rate_up (s t:ℝ)(hs:0<s)(ht:0<t)(σ:ℝ):s^σ=(s/t)^σ*t^σ:=by rw [Real.div_rpow hs.le ht.le,div_mul_cancel₀ _ (Real.rpow_pos_of_pos ht _).ne']

lemma normal_residue_prices (j:ℕ)(σ R:ℝ)(hσ:0<σ)(hR:1 ≤ R): ∃ B:ℝ,0 ≤ B ∧ ∀ (r A t P:ℝ)(F:Full X→Y), F 0=0→ RingPrices j σ r F A → 0 < t → ∀ f:Full X, Fits r f→ Fits (R*t) f → Charge j t (f:X→ℂ) P → Mass (based F f) (B*A*P*t^σ):=by
   let R':=2*R; have ht:1 ≤ R':=by unfold R'; linarith only [hR]
   have hp :0<R':=zero_lt_one.trans_le ht
   obtain ⟨C,hC,H⟩:= piece_budget (X:=X) j
   obtain ⟨D,hD,h⟩:= cascade (Y:=Y) σ 1 hσ zero_lt_one
   let Z :ℝ:= (R')^j * R'^(σ+1); have hz:1 ≤ Z:= one_le_mul_of_one_le_of_one_le (one_le_pow₀ ht) (Real.one_le_rpow ht (by linarith only [hσ]));
   refine ⟨D*C*Z, mul_nonneg (mul_nonneg hD hC) (zero_le_one.trans hz),fun r A t P F hf hX ht' f hY hL hh=>?_⟩
   let U(i:ℕ):= pitch i / t; let V:= A*C*Z*P*t^σ; have hb:= hh.nonneg; have ha:= hX.1; have hT:0 ≤ t^σ:=Real.rpow_nonneg ht'.le _; have hZ:0 ≤ Z:=zero_le_one.trans hz; have hV:0 ≤ V:=by unfold V; positivity
   have he :Rates σ 1 t V (based F f):=by
       constructor
       · intro i hi
         let s:=pitch i; have ht:0<s:=pitches i
         apply (hX.2 s _ ht (pitch_le i) (Piece s f) (piece_fits hY) (piece_ring ht f) (H s P ht hb f (Estimate.subset (Estimate.scale_le hh ht.le hi) (subset_univ _)))).trans
         change A * (C*P)*s^σ≤ (s/t)^σ*V
         rw [Rate_up s t ht ht' σ]; unfold V
         calc
           _ ≤ ((s/t)^σ) * (A*C*P*t^σ)*Z := by
              apply le_trans ?_ (le_mul_of_one_le_right (by positivity) hz); exact le_of_eq (by ring)
           _ =_ := by ring
       intro i hi
       let s:=pitch i; have he:0<s:=pitches i
       by_cases hlo: R*t < s/2
       · change ‖F (Piece s f)‖ ≤ _; rw [piece_too_high he hL hlo,hf,norm_zero]; exact mul_nonneg (Real.rpow_nonneg (div_nonneg ht'.le he.le) (1:ℝ)) hV
       have hU:(s/t)^(σ+1)≤ R'^(σ+1):= Real.rpow_le_rpow (by positivity) ((div_le_iff₀ ht').2 (by unfold R'; linarith only [le_of_not_gt hlo])) (by linarith only [hσ])
       apply (hX.2 s _ he (pitch_le i) (Piece s f) (piece_fits hY) (piece_ring he f) (H s (R'^j*P) he (by positivity) f (packet_coarse hh ht' he.le hR hL))).trans
       change A * (C*(R'^j*P)) * s^σ ≤ (t/s)^(1:ℝ)* V; rw [Rate_up s t he ht' σ,Real.rpow_one]
       have hh:(s/t)^σ ≤ t/s*R'^(σ+1):=by
          rw [Real.rpow_add (by positivity:s/t>0),Real.rpow_one] at hU
          exact (le_div_iff₀ (show 0<s/t by positivity)).2 hU |>.trans_eq (by field_simp)
       unfold V Z
       calc
        _ ≤ A*(C*(R'^j*P))*((t/s*R'^(σ+1))*t^σ) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hh hT) (by positivity)
        _ =_ := by ring
   exact Mass.mono (h t V ht' hV _ he) (le_of_eq (by unfold V; ring))
lemma normal_portion_prices (j m:ℕ)(σ R:ℝ)(hR:1 ≤ R)(hσ:0 < σ+(m:ℝ)+1)(hs:σ+(m:ℝ)<0):
   ∃ B:ℝ,0 ≤ B ∧ ∀ (r A t P s:ℝ)(F:Full X→Y), RingPrices j σ r F A → 0 < t →0<s→2*s≤r→t ≤ R*s → ∀ f:Full X, Fits r f→ Fits (R*t) f → Charge (j+m+1) t (f:X→ℂ) P → Mass (based F (leftOut s m f)) (B*A*P*t^σ):=by
   let a:=σ+m+1; let b:= -(σ+(m:ℝ)); obtain ⟨C,hC,H⟩:= cascade (Y:=Y) a b hσ (neg_pos.2 hs); obtain ⟨D,hD,h⟩:= piece_budget (X:=X) j
   obtain ⟨U,hU,hu⟩:=left_near (X:=X) m j R hR; obtain ⟨V,hV,hv⟩:= left_coarse (X:=X) m j R hR
   refine ⟨C*D*(U+V),mul_nonneg (mul_nonneg hC hD) (add_nonneg hU hV),fun r A t P s F hF ht hs' hh hh' f hf hp hX=>?_⟩
   let x:= leftOut s m f; let M:=D*(U+V)*A*P*t^σ; have hP:= hX.nonneg; have hA:=hF.1; have hM:0 ≤ M:=by unfold M; positivity
   have hg:= left_fits hs' m hf hh
   have he(i:ℕ) (Q:ℝ) (hQ:0 ≤ Q) (he:Estimate j (pitch i) (x:X→ℂ) (Ringed X (pitch i)) Q):
       ‖based F x i‖ ≤ A*(D*Q)*pitch i ^σ:=hF.2 _ _ (pitches i) (pitch_le i) _ (piece_fits hg) (piece_ring (pitches i) x) (h (pitch i) Q (pitches i) hQ x he)
   have hS: Rates a b t M (based F x):=by
       constructor
       · intro i hi
         let p:=pitch i; have hl:0<p:=pitches i
         apply (he i _ (by positivity:0 ≤ U*P*(p/t)^(m+1)) ( Estimate.subset (hu t ht s hh' p hl hi f P hX) (fun _ h=> rings_inside h))).trans
         change A*(D*(U*P*(p/t)^(m+1)))*p^σ ≤ (p/t)^a*M
         have hy:(p/t)^a=(p/t)^σ*(p/t)^(m+1):=by
            rw [show a=σ+((m+1:ℕ):ℝ) by simp [a,add_assoc],Real.rpow_add (by positivity:p/t>0),Real.rpow_natCast]
         rw [hy,Rate_up p t hl ht σ]; unfold M
         calc
           _ ≤ A*(D*((U+V)*P*(p/t)^(m+1)))*((p/t)^σ*t^σ) := by gcongr; linarith only [hV]
           _ =_ := by ring
       intro i hi
       let p:=pitch i; have hl:0<p:=pitches i
       apply (he i _ (by positivity:0 ≤ V*P*(p/t)^m) (hv t s p ht hs' hi f P hp (Estimate.lower hX (by omega)))).trans
       change A*(D*(V*P*(p/t)^m))*p^σ ≤ (t/p)^b*M
       have hy:(t/p)^b=(p/t)^σ*(p/t)^m:=by
          unfold b; rw [Real.rpow_neg_eq_inv_rpow, inv_div,Real.rpow_add (by positivity:p/t>0),Real.rpow_natCast] -- check
       rw [hy,Rate_up p t hl ht σ]; unfold M
       calc
           _ ≤ A*(D*((U+V)*P*(p/t)^m))*((p/t)^σ*t^σ) := by gcongr; linarith only [hU]
           _ =_ := by ring
   exact Mass.mono (H t M ht hM (based F x) hS) (le_of_eq (by unfold M; ring))
end YM.Frontier6.Normal
