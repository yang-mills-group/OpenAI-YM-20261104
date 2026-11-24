import YM.FVA2.O.Dust.Cotton
/-!
# Full products satisfy the Ward condition exactly

Pointwise version of the past-smallness property, using separated shapes and
previous `Sweep` estimates. `Response`: the whole `helm` condition and the rank
upper bound etc.; with this, a response tending to zero at t → -∞ actually
vanishes identically. Prove the Ward closure by this argument (`safe_Ward`).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Cool
open MS Function Filter Set Finset MS.Plane MS.Koszul Flux MeasureTheory MS.Heat MS.Book Convolve Signal
open MS.Breeze MS.Latch MS.Osc MS.Osc.Snap MS.Fiddle MS.Garment MS.Garment.Wick MS.Rock MS.Rock.Path MS.City MS.Rake MS.Tone Momentum MS.Landau Detect MS.Color Real MS.Tide
open Ward Job Wire MS.Local.Physical MS.Land Lives Puff Serve Rake.Geo Vane Actors Fuse Job.Belt
open scoped Topology ContDiff Interval
variable {G:Gauge}{I:Type}{F H:Glade G I}{a b:I→QP}{P:Geo I}{B:Deck G}{K:Booked B}{M:MS_Data G K}{X:T (Glade G I)}{q:ℤ}{η:I→ℝ} {l:I→Filter ℝ}
abbrev PastPoint (F:Glade G I): Prop:= ∀ i (l:Legs (Lane4 G)),Tendsto (fun s=> F i s l) atBot (𝓝 0)
lemma limitN (h:Nilp P F): PastPoint F:= by
    intro i l; let T:= Lower P; let w:= ray l; let q:ℤ:= 1-pitch w; obtain ⟨ C,hC,k,hk⟩:= Costs.norm_cost ( h q ℝ w (fun z=>Bool.noConfusion z) (fun z=>Bool.noConfusion z) ); let V:= habitat P i; have hV: 0<V:= by unfold V habitat; positivity
    have ht : Tendsto (fun t:ℝ=> C*(2*V)^k*LogTime.polyExp 1 k (-t)) atBot (𝓝 0) := by simpa only [Function.comp_def,mul_zero] using ( (LogTime.vanishes ( by norm_num : (0:ℝ)<1 ) k ).comp tendsto_neg_atBot_atTop ).const_mul ( C*(2*V)^k )
    apply tendsto_zero_iff_norm_tendsto_zero.mpr; apply squeeze_zero' (Eventually.of_forall fun i=> norm_nonneg _) _ ht; filter_upwards [eventually_le_atBot (0:ℝ)] with t ht;
    let p:(east P false).time:= ⟨ i,t,ht⟩; specialize hk p (1:ℝ) trivial; simp only [w,Chart,plug,ray_sail] at hk; refine hk.trans ?_; simp only [ Scale.full, Lower, Below,stamp, Scale.weight, coldE, show tstart p=t from rfl, show (east P false).price.basic p=V*(1+|t|) from rfl, abs_of_nonpos ht, show ‖(1:ℝ)‖=(1:ℝ) by simp, ← zpow_add₀ (exp_pos t).ne', show pitch (ray l)+q=1 from (by unfold q w; omega),zpow_one,mul_one,LogTime.polyExp, neg_one_mul, neg_neg ]
    calc
       _ ≤ C*( V*(1+-t)*(1+1) )^k * exp t:= by
           have hc:0≤ -t:= by linarith
           gcongr; exact exp_le_one_iff.mpr ht
       _ = _:= by simp only [mul_pow,one_add_one_eq_two]; ring
lemma forget (h:Response X M η q)(l:I→Filter ℝ)[∀ i: I,(l i).NeBot](hp:∀ n i (w:Legs (Lane4 G)),Tendsto (fun t=>X n i t w) (l i) (𝓝 0)): X=0:= by
    funext n; induction n using Nat.strong_induction_on with | h n IH=>
    have hm:= h.life n; obtain ⟨k,hk⟩:= hm.heat; let F:= X n; have hv : helm M η X n=(both G I).P F:= by rw [hel_core,lonely,Finset.sum_eq_zero,add_zero]; intro i hi; rw [IH i ( Finset.mem_Ico.mp hi|>.2 )]; exact map_zero ((both G I).X _)
    obtain hV:= h.vital n; rw [hv] at hV;
    funext i t w; let Z(p:ℕ):Prop:= ∀ t (w:Legs (Lane4 G)),w.length+p>k→ F i t w=0; suffices he:∀ p,Z p from he (k+1) _ _ (by omega); intro p; induction p with
    | zero=> intro t w hw; exact hk i t w (by omega)
    | succ p ip=>
       intro t w hw; have he(s:ℝ): HasDerivAt (fun s:ℝ=> X n i s w) 0 s:= by obtain he:=hV i s w; change HasDerivAt _ ( Heat.orbit ( lineA G s ) planeF ( F i s ) w ) s at he; convert he using 1; rw [finite_cc planeF (rA.pays Geo.Coherent hm.invoice)]; unfold Ccy; simp_rw [ at_trc, show ∀ u v:Lane4 G, X n i s (u::v::w)=0 from fun _ _=> ip s _ (by simp; omega),mul_zero, Finset.sum_const_zero ]; simp
       exact tendsto_nhds_unique (show Tendsto (fun p=> X n i p w) (l i) (𝓝 (F i t w)) from tendsto_const_nhds.congr (fun k=> is_const_of_deriv_eq_zero (fun s=>(he s).differentiableAt) (fun s=>(he s).deriv) t k)) (hp n i w)
variable {W:Type}[LinearOrder W]{x:Position W I}{R:W→ Rake.Label B}{U:Rake.Dance G I W}
theorem safe_Ward (h: Mesh P x)(ht:P.θ=0)(hp:∀ i,Fixed (x i))(he:DOrd K P M R x U) (s: Finset W): Certified ( plenum x U s ) M P.η 0:= by
    obtain hh:= plenum_R he (world_price h he) s; exact ⟨hh, forget hh.ward.1 (fun _=>atBot) (fun n=> limitN ( tContext h ht he hp n ))⟩
end YM.FVA2.O.Cool
