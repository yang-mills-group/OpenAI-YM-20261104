import YM.MergeProof.North.Lauder
import YM.Frontier6.Multi.Toll.Pitch

/-! Sustaining chosen stop costs at a prescribed valuation. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Road.Fareway
open Function Filter Lattice RG Push Set Finset Topology MergeProof.Ribbons
open scoped Topology BigOperators Classical
variable {I:Type*}{T:Fareway I}{G:Gauge}(C:Family G)
section
variable (S:Schedule)
structure Bench (T:Fareway I)(j:I→ℕ)(a:ℝ):Prop where
    infinite : Tendsto j T.via atTop
    speed : Tendsto (fun i=> S.scale (j i)/T.scale i) T.via (𝓝 a)
variable {S}{j k:I→ℕ}{a b:ℝ}{f:ℕ→ℝ}
namespace Bench
variable (h:Bench S T j a)
include h
lemma notes (hh:Note S f b): T.Mint (fun i=> f (j i)) (b*a):=by
   refine ⟨Eventually.of_forall (fun i=>hh.pos _), ((hh.pitch.comp h.infinite).mul h.speed).congr' ?_⟩
   filter_upwards [(S.divergent.comp h.infinite).eventually_gt_atTop 0] with i hi; dsimp only [comp_apply]; have hx:0< S.scale (j i):=hi; field_simp
lemma later (hs:Bench S T k b)(he:a<b): ∀ᶠ i in T.via, j i < k i:=by
   let y:=(a+b)/2; have hp:a<y:=by unfold y; linarith
   filter_upwards [h.speed.eventually (gt_mem_nhds hp),hs.speed.eventually (lt_mem_nhds (show y<b by unfold y; linarith)),T.ahead] with i hi he hg; exact (bob S).lt_iff_lt.mp ((div_lt_div_iff_of_pos_right hg).mp (lt_trans hi he))
lemma spacing : T.Mint (fun i=> S.a (j i)) (-a):= by simpa only [neg_one_mul] using h.notes (Note.note_a ..)
lemma succ (hf:S.Gentle): Bench S T (fun i=> j i+1) a:=by
   refine ⟨(tendsto_add_atTop_nat 1).comp h.infinite,?_⟩; have hh:= Note.bell_exp S 1|>.scales hf; have he:= h.notes hh|>.pitch; simp_rw [Real.log_exp,one_mul] at he; exact he
end Bench
lemma picks (S:Schedule)(hf:S.Gentle)(T:Fareway I)(a:ℝ)(ha:0<a):∃ j:I→ℕ,Bench S T j a:=by
    have he(i:I) : ∃ j:ℕ, a*T.scale i≤ S.scale j:= (S.divergent.eventually_ge_atTop _).exists
    let j i:= Nat.find (he i); have hz(i): a*T.scale i≤ S.scale (j i):= Nat.find_spec (he i)
    have hu:Tendsto (fun i=>a*T.scale i) T.via atTop:= Tendsto.const_mul_atTop ha T.follows
    have hv:Tendsto j T.via atTop:= tendsto_atTop.2 fun b=> by filter_upwards [hu.eventually_ge_atTop (S.scale b)] with i hi; exact (bob S).le_iff_le.mp (le_trans hi (hz i))
    let k i:=j i-1; have hK:Tendsto k T.via atTop:= tendsto_atTop.2 fun b=> (hv.eventually_ge_atTop (b+1)).mono fun i hi=>by unfold k; omega
    have hy:= ((barbell S hf).comp hK); refine ⟨j,hv,tendsto_of_tendsto_of_tendsto_of_le_of_le' (h:=fun i=> a*(S.scale (k i+1)/S.scale (k i))) tendsto_const_nhds (by simpa only [mul_one] using! hy.const_mul a) ?_ ?_⟩
    · filter_upwards [T.ahead] with i hi; exact (le_div_iff₀ hi).mpr (hz i)
    filter_upwards [T.ahead,(S.divergent.comp hK).eventually_gt_atTop 0,hv.eventually_gt_atTop 0] with i hi hK' hv'
    have hM:0<S.scale (k i):=hK'; have he':k i+1=j i:=by unfold k; omega
    have hP:S.scale (k i)< a*T.scale i:=lt_of_not_ge (Nat.find_min (he i) (show k i< j i by omega)); let v:=S.scale (j i)/S.scale (k i); have hp:v≥0:=div_nonneg ((hM.trans_le ((bob _).monotone (by omega))).le) hM.le
    rw [he',(div_le_iff₀ hi)]; exact le_trans (Eq.symm (show v*S.scale (k i)= _ from div_mul_cancel₀ _ hM.ne')|>.le) ((mul_le_mul_of_nonneg_left hP.le hp).trans_eq (by change v*_ = a*v*_; ring))
end

-- the fuel register minimality gives K/J log rates equal & stakes subpower at *moving* J
lemma fiat_floor (A:Levels G)(r:ℕ) : 1 ≤ Vac.fiat G (A.params r) (A.clock.hatBeta r) := by
    unfold Vac.fiat; have he := (A.params r).paths_pos; have ha := (A.params r).clip.quadratic_pos
    have hp : 0≤ (Fintype.card PlaqAxes:ℝ)*((A.params r).clip.direct + (A.params r).paths^2) + 4*Module.finrank ℝ G.Mat*(Real.log 16+Real.log (A.clock.hatBeta r)/2) := by
      have hu := Real.log_pos (A.fits.delayed r); positivity
    linarith only [hp,he]
lemma gap_cost (A:Levels G)(h:Stock.Tabs A)(ε:ℝ)(he:0<ε): ∀ᶠ i:ℕ in atTop,let k:=Stock.Tabs.chosen A 1 h i; A.S.scale k-A.S.scale i ≤ ε*A.S.scale k:=by
   filter_upwards [Stock.Tabs.pay A 1 h le_rfl ε he] with i hi; let k:=Stock.Tabs.chosen A 1 h i
   intro j; let q:= A.S.a i/A.S.a k; have hu:1 ≤ q := (one_le_div (A.S.a_pos _)).2 (A.S.strictAnti.antitone (Stock.Tabs.opened _ _ _ i).1)
   change A.S.scale k- _ ≤ ε* A.S.scale k; rw [show A.S.scale k-A.S.scale i = Real.log q from (by unfold Schedule.scale q; rw [Real.log_div (A.S.a_pos _).ne' (A.S.a_pos _).ne',Real.log_inv,Real.log_inv]; ring)]
   exact (Real.log_le_self (zero_le_one.trans hu)).trans (((pow_one q).symm.trans_le (pow_le_pow_right₀ hu (show 1 ≤ 4 by norm_num))).trans ((le_mul_of_one_le_right (pow_nonneg (zero_le_one.trans hu) _) (fiat_floor A k)).trans hi))
lemma balanced (A:Levels G)(h:Stock.Tabs A): Tendsto (fun i=> A.S.scale (Stock.Tabs.chosen A 1 h i)/A.S.scale i) atTop (𝓝 1):= (Metric.tendsto_nhds).mpr fun ε he=>by
    let e:= ε/(2*(1+ε)); have he':0<e:=by unfold e; positivity
    filter_upwards [gap_cost A h e he',A.S.divergent.eventually_gt_atTop 0] with i hh hi;
    let k:=Stock.Tabs.chosen A 1 h i; change dist (A.S.scale k / A.S.scale i) _ < _; rw [Real.dist_eq]; apply abs_lt.mpr; have hm:A.S.scale i ≤ A.S.scale k:= (bob _).monotone (Stock.Tabs.opened _ _ _ _).1; refine ⟨lt_of_lt_of_le (by linarith only [he] : -ε<0) (sub_nonneg.mpr ((one_le_div hi).mpr hm)), sub_lt_iff_lt_add.mpr ((div_lt_iff₀ hi).mpr ?_)⟩
    change A.S.scale k-A.S.scale i ≤ e* A.S.scale k at hh; unfold e at hh; field_simp at hh; -- derive
    nlinarith only [mul_pos he hi,hh, mul_nonneg he.le (sub_nonneg.mpr hm), mul_le_mul_of_nonneg_left hh he.le]
section
set_option quotPrecheck false
local notation "A"=> C.path.levels
variable (h : Stock.Tabs C.path.levels){j:I→ℕ}{a:ℝ}(ht:Bench C.S T j a)
local notation "k"=> fun i=> Stock.Tabs.chosen C.path.levels 1 h (j i)
include ht h
lemma chosen : Bench C.S T (fun i=> Stock.Tabs.chosen A 1 h (j i)) a:=by
    refine ⟨tendsto_atTop_mono' T.via (Eventually.of_forall fun i=>(Stock.Tabs.opened _ _ _ _).1) ht.infinite,?_⟩
    have hx:= ((balanced A h).comp ht.infinite).mul ht.speed ;rw [one_mul] at hx; refine hx.congr' ?_
    filter_upwards [(C.S.divergent.comp ht.infinite).eventually_gt_atTop 0] with i hi; have he:0 < C.S.scale (j i):=hi; dsimp only [comp_apply]; field_simp -- check

open MergeProof
lemma tickets (ha:0<a) (hG:G.Simple) : T.Costs (fun i=> Accent.stakes C (j i) (Stock.Tabs.chosen A 1 h (j i))) 0:=by
   intro b hb; let u:= b/(4*a); have hu:0<u:= by unfold u; positivity
   have hx:= chosen C h ht
   filter_upwards [ ht.infinite.eventually (Stock.Tabs.pay A 1 h le_rfl u hu),hx.infinite.eventually (Vac.treasury_stage A hG), hx.speed.eventually (gt_mem_nhds (show a < 2*a by linarith)), T.follows.eventually_gt_atTop (10/b), T.ahead] with i hi hr hv hq hL
   unfold Accent.stakes; rw [Real.norm_of_nonneg (Real.exp_pos _|>.le)]; apply Real.exp_monotone; let s:ℝ := C.S.a (j i)/C.S.a (k i)
   have ht : s^4*Vac.treasury A (k i) ≤ u*C.S.scale (k i):= (mul_le_mul_of_nonneg_left hr (by positivity)).trans hi;
   have hg : C.S.scale (k i) ≤ (2*a)*T.scale i:=((div_lt_iff₀ hL).1 hv).le
   have hd := mul_le_mul_of_nonneg_left hg hu.le
   have hF:(T.scale i)*b/2≥5:=by linarith only [(div_lt_iff₀ hb).mp hq]
   have hH:u*(2*a*T.scale i)=T.scale i*b/2:=by unfold u; field_simp; ring
   rw [hH] at hd; change s^4*Vac.treasury A (k i)+5 ≤ _; linarith only [hF,ht,hd]
end
end YM.Frontier6.Road.Fareway
