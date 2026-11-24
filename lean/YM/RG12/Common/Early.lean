import YM.Pert.Dense.Portal
/-!
# Price Viability at \\log(length log) separations

Strengthen the wait calculus in Voucher: the Rank supplier uses only windows
consuming *o(log age)* at fixed commissioning horizon and stage. Preserve that claim in the
constructors rather than relying on the final Wait to satisfy it after several additional
commissions! These ports adapt proofs of honoured/served/tabled in the seed (Next RANK), to the
stronger asymptotics; no change to Stamp costs or any local analytic obligations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Commission
open Function Filter Lattice Wilson RG RG.Supply Next.Rank Next.Rank.Tapes Next.Rank.Perch Next.Rank.Station Real Asymptotics Ship Peak
open scoped Topology BigOperators
variable {G:Gauge}{p:Sheet G}{w:Rolls p}{θ:Protection w}{H:Delays θ}{B:Bar H}

def Early (U:Wait B):Prop:=∀ i, Tendsto (fun x:ℝ=> (U.window i x:ℝ)/Real.log (preHat B x)) atTop (𝓝 0)
-- price ceil
private lemma ceil_cost (x g:ℝ→ℝ)(h:Tendsto (fun i=>x i/g i) atTop (𝓝 0))(hg:Tendsto g atTop atTop) (hx:∀ᶠ i in atTop,0≤x i):
    Tendsto (fun i=>(Nat.ceil (x i):ℝ)/g i) atTop (𝓝 0):=by
  apply squeeze_zero' (g:=fun i => x i/g i+1/g i)
  · filter_upwards [hg.eventually_gt_atTop 0] with i hi; positivity
  · filter_upwards [hg.eventually_gt_atTop 0,hx] with i hi hx; rw [← add_div]; exact div_le_div_of_nonneg_right (Nat.ceil_lt_add_one hx).le hi.le
  simpa only [add_zero] using h.add (tendsto_const_nhds.div_atTop hg)
private lemma chamber {x b:ℝ}(hx:1<x)(hb:0≤b): Tendsto (fun s:ℝ=> ((bump x b s+more x s:ℕ):ℝ)/Real.log s) atTop (𝓝 0):=by
  let d(t:ℝ):= Real.log t; let c:=d x; let f(t:ℝ):=d (d t)^2
  have hd:0<c:=Real.log_pos hx; let v:=YM.Vac.Numbers.P
  have h0:Tendsto (fun t=> f t/d t) atTop (𝓝 0):=by simpa only [one_mul,f,v,d] using (YM.Vac.Numbers.monitor 1)
  have hn(t):0<v t:=Real.exp_pos _
  have ef(t):d (v t ^ b*v t ^ (2:ℕ))=(b+2)*f t:=by
    change Real.log (v _ ^b*v _ ^(2:ℕ))= _; rw [Real.log_mul (by positivity [hn t]) (by positivity [hn t]),Real.log_rpow (hn t),Real.log_pow]; unfold v YM.Vac.Numbers.P; rw [Real.log_exp];push_cast; unfold f d; ring
  have hv := ceil_cost (fun t=>d (v t^b*v t^2)/c) d ?_ (Real.tendsto_log_atTop) (Eventually.of_forall fun i=>by rw [ef]; unfold f; positivity)
  rotate_left 1
  · have he:= (h0.const_mul (b+2)).div_const c; rw [mul_zero,zero_div] at he; exact he.congr (fun x=>by rw [ef]; unfold f; ring)
  let a(t):=(Nat.ceil (d t^2):ℝ)
  have H : ∀ᶠ i in atTop,1 ≤ a i ∧ a i ≤ (d i)^2+1:=by
    filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1] with i hi
    have hi : 1≤d i:=hi
    exact ⟨le_trans (one_le_pow₀ (n:=2) hi) (Nat.le_ceil _),(Nat.ceil_lt_add_one (sq_nonneg _)).le⟩
  have hx:Tendsto (fun i=> (d (a i)/d i)) atTop (𝓝 0):=by
    have he : Tendsto (fun i=>d (d i)/d i) atTop (𝓝 0):=by simpa [d,Function.comp_def] using (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp Real.tendsto_log_atTop)
    have hc := (he.const_mul 2).add (tendsto_const_nhds (x:=d 2)|>.div_atTop Real.tendsto_log_atTop); rw [mul_zero,add_zero] at hc
    apply squeeze_zero' _ _ hc
    · filter_upwards [H,Real.tendsto_log_atTop.eventually_ge_atTop 1] with i hi hs using div_nonneg (Real.log_nonneg hi.1) (by unfold d;linarith)
    filter_upwards [H,Real.tendsto_log_atTop.eventually_ge_atTop 1] with i hi hs
    have h1: 0<d i:=lt_of_lt_of_le (by norm_num) hs
    have ht:d (a i)≤d (2*(d i)^2):=Real.log_le_log (zero_lt_one.trans_le hi.1) (hi.2.trans (by change (Real.log i)^2+1 ≤ 2*Real.log i^2; nlinarith))
    apply (div_le_div_of_nonneg_right ht h1.le).trans_eq; unfold d; rw [Real.log_mul (by norm_num) (by positivity [h1]),Real.log_pow]; push_cast; ring
  have hf := ceil_cost (fun t=> d (a t ^ (10:ℕ))/c) d ?_ Real.tendsto_log_atTop (H.mono fun i hi=> div_nonneg (Real.log_nonneg (one_le_pow₀ hi.1)) hd.le)
  rotate_left 1
  · have ht:= (hx.const_mul 10).div_const c; rw [mul_zero,zero_div] at ht; exact ht.congr (fun t=>by unfold d; rw [Real.log_pow]; push_cast; ring)
  have he:= hv.add hf; rw [add_zero] at he
  exact he.congr (fun i=>by rw [Nat.cast_add,add_div];rfl)
lemma allotted (b : ℝ) (j:ℕ)(h:G.Simple)(hb:0≤b): Tendsto (fun s=> (benchCost B b j s:ℝ)/Real.log (preHat B s)) atTop (𝓝 0):=by
  have hva:Tendsto (preHat B) atTop atTop:=Filter.tendsto_atTop_add_const_left _ _ (Tendsto.const_mul_atTop (Gauge.slopeConstant_pos h) tendsto_id)
  exact (chamber (lt_of_lt_of_le (by norm_num : (1:ℝ)<3) (show 3≤((w.L j).val:ℝ) from by exact_mod_cast (w.large j).size)) hb).comp hva
open Finset
lemma expedited {U : Wait B}(hz:Early U) (h:G.Simple) (O : HaarBudget G)(m : ℕ→ℕ)(a:ℕ→ℝ)(E: ℕ→ℕ→Era)(J:ℕ→ Finset ℕ)(hm:∀ i,0 < m i)(hA:∀ i,0≤a i):∃ W:Wait B, Early W ∧ U.minLength ≤ W.minLength ∧ (∀ j,U.readyHere j ≤ W.readyHere j ∧ ∀ s,U.window j s ≤ W.window j s) ∧ ∀ j i,i∈J j → Fired B W O j (a i) (m i) (E j i):=by
  have he (j : ℕ) : ∀ᶠ s in atTop,∀ i∈ J j, cardTest B O j (m i) (a i) (E j i) s :=
    (eventually_all_finset _).2 (fun i _ => reserves B h j _ (hm i) _ (hA i) (E j i) O)
  choose v hv using fun j => eventually_atTop.mp (he j)
  let z (j : ℕ) (s : ℝ) := ∑ i∈J j,benchCost B (a i) j s
  let W : Wait B := { U with
    readyHere := fun j => max (U.readyHere j) (v j)
    window := fun j s => U.window j s+z j s
    sublin j := by
      have ht : Tendsto (fun s => (z j s:ℝ)/s) atTop (𝓝 0) := by
        have he := tendsto_finsetSum (J j) (fun i _ => accommodate B (a i) j h (hA i))
        simpa [z,Finset.sum_div] using! he
      simpa [add_div] using! (U.sublin j).add ht }
  refine ⟨W,?_,le_rfl,fun j => ⟨le_max_left ..,fun s => Nat.le_add_right ..⟩,fun j i hi s hx => ?_⟩
  · intro j
    have hw:= (hz j).add (tendsto_finsetSum (J j) (fun i _=> allotted (a i) j h (B:=B) (hA i)))
    simpa [W,z,add_div,Finset.sum_div] using! hw
  exact ⟨hv j s ((le_max_right ..).trans hx) i hi,(Finset.single_le_sum (f:=fun i => benchCost B (a i) j s) (fun _ _ => Nat.zero_le _) hi).trans (Nat.le_add_left ..)⟩
lemma tabled (h : G.Simple) (A : Wait B)(hB:Early A) (k : ℕ → Finset ℕ) (O : HaarBudget G) (G₀ : ℕ → ℕ → Purse) (M : ℕ → ℝ)
    (b : ℕ→ℝ) (hb : ∀ j,0≤ b j) (he : ∀ i,0≤M i) (hh : ∀ i j,(G₀ i j).band=b i) (hp : ∀ i j,i∈k j → Regiment (G₀ i j) (p.profile j) (w.L j)) :
    ∃ A' : Wait B,Early A'∧ A.minLength ≤ A'.minLength ∧ (∀ j,A.readyHere j≤ A'.readyHere j ∧ (∀ s,A.window j s ≤ A'.window j s)) ∧
      ∀ i j,i∈ k j → ReadyRack O j (G₀ i j) (M i) A':= by
  obtain ⟨W,hE,hW,hZ,hv⟩:= expedited hB h O (fun _=> 2) b (fun i j=> (G₀ j i).era) k (fun _=>by norm_num) hb
  have hl: Tendsto (preHat B) atTop atTop:= Filter.tendsto_atTop_add_const_left _ _ (tendsto_id.const_mul_atTop (Gauge.slopeConstant_pos h))
  have ht (j) := (eventually_all_finset (k j)).2 (fun i hi=> hl.eventually (annually (p:=G₀ i j) (G:=G) _ (M i) (hp i j hi) (he i)))
  choose t hs using fun j=> eventually_atTop.mp (ht j)
  let p: Wait B := { W with readyHere := fun j=> max (W.readyHere j) (t j) }
  refine ⟨p,hE,hW,fun j=>⟨(hZ j).1.trans (le_max_left ..), (hZ j).2⟩,fun i j h=>⟨fun s hj=> ?_,fun s hk=>?_⟩ ⟩
  · rw [hh]; exact hv j i h s ((le_max_left _ (t j)).trans hj)
  exact hs j s ((le_max_right _ _).trans hk) _ h
end YM.RG12.Commission
