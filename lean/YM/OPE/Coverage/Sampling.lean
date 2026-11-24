import YM.OPE.Coverage.Trench
/-! ## Sampling through the plateau edges on a funded timetable -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Coverage
open Function Filter Set Lattice Wilson RG Next.Rank Bid Push.PriceCompiler Precision Supply Real Station Ship
open scoped Topology Classical
variable {G : Gauge} {X:Sheet G} {w:Rolls X} {D:Protection w} {T T':Delays D}{Z:Bar T}{Z':Bar T'}{I:Wait Z}{I':Wait Z'} {A:Levels G}
set_option quotPrecheck false
local notation "J" => A.clock.J
local notation "Y" => A.S.scale
local notation "len" => fun j=>((w.L j).val:ℝ)
local notation "Xhat" => fun k=>Ship.preHat Z (Y k)
local notation "depth" => fun b k=>Ship.benchCost Z b (A.clock.J k) (A.S.scale k)
local notation "seam" => frontier A

theorem scales_route (A:Levels G) : Monotone A.S.scale:=monotone_nat_of_le_succ fun i=>by
     rw [A.S.scale_succ]
     apply le_add_of_nonneg_right; exact Real.log_nonneg (by exact_mod_cast (A.S.block i).property)

lemma surface (v:ℝ→ℕ→ℝ) (hv:v Z.value = I.readyHere)(hB:Z.value=Z'.value)(hU:DelayLe (reset T v) T') (hA:Paid (supplement I I') A) : Loft I A where
    paid := pay_across ((reset_up T v).trans hU) hB (le_sup_left ..) (fun i=>le_max_left ..) (fun j s=>(Nat.le_add_right ..).trans (Nat.le_add_right ..)) hA
    tail := by
       filter_upwards [A.fits.deep.eventually_gt_atTop X.first,eventually_ge_atTop (1:ℕ)] with i hi hl
       let j:= J i
       have h : j= A.clock.J (i-1+1):=by rw [Nat.sub_add_cancel hl]
       change X.first < j at hi
       have he := hU.scale j Z'.value
       have hk : T'.scaleEntry j Z'.value ≤ Y i :=((h.symm ▸ (hA.paysHigher (i-1) (h ▸ hi)) : T'.scaleEntry j Z'.value ≤ Y (i-1)) |>.trans (scales_route A (Nat.sub_le ..)))
       change _ ∧ I.readyHere j ≤ Y i ∧ _
       have hr : exp (↑↑(w.L j):ℝ) ≤ exp (exp (↑↑(w.L j):ℝ)):= by linarith only [add_one_le_exp (exp (↑↑(w.L j):ℝ))]
       have hx := max_le_iff.mp ((max_le_iff.mp (show (reset T v).scaleEntry j Z'.value ≤ Y i from he.trans hk)).2)
       have hw : exp (↑↑(w.L j):ℝ) ≤ Y i:=hr.trans hx.2
       exact ⟨hi,hv ▸ hB ▸ hx.1,hw⟩
    aisles j hj :=by obtain ⟨k,-,he,hm⟩:=hA.run j hj
                     have h : round (Y k) ≤ (supplement I I').window j (Y k) :=Nat.le_add_left ..
                     exact ⟨k,h.trans he,fun m hf hn=> hm m ((Nat.sub_le_sub_left h _).trans hf) (hn.trans (Nat.le_add_right ..))⟩

def previous (A:Levels G)(i:ℕ):= frontier A i -1
lemma previous_runs : Tendsto (previous A) atTop atTop:=by
    refine tendsto_atTop_atTop.mpr (fun m=>?_)
    obtain ⟨k,hK⟩:=eventually_atTop.mp ((seam_late (A:=A)).eventually_ge_atTop (m+1))
    exact ⟨k,fun i hi=> by have h:=hK _ hi; unfold previous; omega⟩
omit Z T D w X in
lemma previous_last {i:ℕ}(h:0<seam i): terminal A (previous A i):=by
    intro m hm; by_contra! he
    have ht:seam i ≤ m:=Nat.le_of_not_gt (fun hp=>not_lt_of_ge (show m≤frontier A i-1 by omega) he)
    have hk:= A.fits.mono ht; change A.clock.J m=A.clock.J (seam i-1) at hm
    rw [hm] at hk
    have hv:J (seam i-1)=J i:=le_antisymm (A.fits.mono ((Nat.sub_le ..).trans (seam_early _))) ((seam_stable i) ▸ hk)
    exact Nat.lt_irrefl _ ((Nat.sub_one_lt_of_lt h).trans_le (seam_min hv))

lemma wide (b:ℝ)(i:ℕ)(h: depth b i ≤ i-seam i): stationReady Z A b i:= ⟨h.trans (Nat.sub_le ..),fun j hj he=> le_antisymm (A.fits.mono he) (by rw [←seam_stable i]; exact A.fits.mono ((by have hQ:= seam_early (A:=A) i; omega : seam i ≤ i-(depth b i)) |>.trans hj))⟩

def Hop (Z:Bar T) (b:ℝ) (A:Levels G) (i:ℕ):= if Ship.benchCost Z b (A.clock.J i) (A.S.scale i) ≤ i-frontier A i then i else previous A i

local notation "stopover" => Hop Z

variable (H:Loft I A)
lemma hop_large(b:ℝ): Tendsto (stopover b A) atTop atTop:= by
     apply tendsto_atTop_mono (f:=previous A)
     · intro i; change previous A i ≤ stopover b A i
       dsimp only [Hop]; split_ifs
       · exact (Nat.sub_le ..).trans (seam_early _)
       exact le_rfl
     exact previous_runs

include H
omit Z' I' in
lemma carriage (hG:G.Simple)(b:ℝ)(hb:0≤b):
     ∀ᶠ k in atTop, stationReady Z A b (stopover b A k) := by
     have hg: ∀ᶠ k:ℕ in atTop,0 < seam k:= (seam_late (A:=A)).eventually_gt_atTop _
     filter_upwards [hg, (previous_runs (A:=A)).eventually (tail_permit (H:=H) hG b hb)] with k hp ht
     dsimp only [Hop]; split_ifs with hx
     · exact wide b k hx
     exact ht (previous_last hp)
omit H
include H
lemma wheel_room (h:G.Simple): ∀ᶠ i in atTop, wheel A i ≤ A.clock.monitor i:=by
   let α:= G.slopeConstant
   have ha:0<α:=Gauge.slopeConstant_pos h
   let x:= A.clock.hatBeta
   have hB: Tendsto (fun k=>log (log (x k))) atTop atTop:= tendsto_log_atTop.comp (tendsto_log_atTop.comp (hat_rate A h))
   filter_upwards [hB.eventually_ge_atTop 2, H.tail, (tendsto_log_atTop.comp (hat_rate A h)).eventually_ge_atTop (2+|log α⁻¹|), (hat_rate A h).eventually_gt_atTop 1] with k hk he hl hx
   rw [wheel,H.paid.lengths]; let n:=len (J k); let y:= x k
   have hy:1<y:=hx
   suffices n ≤ exp (log (log y)^2) from this
   have he : exp n ≤ y*α⁻¹:= by
       apply he.2.2.trans; rw [← div_eq_mul_inv,le_div_iff₀ ha]; unfold y x α
       exact (show A.S.scale k*G.slopeConstant≤A.clock.bar+ G.slopeConstant*A.S.scale k by linarith only [A.clock.bar_pos])
   have hm := log_le_log (exp_pos _) he
   rw [log_exp, log_mul (by linarith) (inv_ne_zero ha.ne')] at hm
   have hcL: 0<log y:=log_pos hy
   have hr : log y ^ 2 ≤ exp (log (log y)^2):=by
       rw [sq,← exp_log hcL,← exp_add,log_exp]
       exact exp_monotone (by nlinarith)
   change 2 + |log α⁻¹| ≤ log y at hl
   have hx : |log α⁻¹| ≤ log y:=by linarith
   have ht : 2 ≤ log y := by linarith [abs_nonneg (log α⁻¹)]
   have h:=le_abs_self (log α⁻¹)
   linarith only [hm,h,mul_nonneg (show 0≤log y-2 by linarith only [ht]) hcL.le,hx,hr]
omit H
include H
lemma small_journey {b₁ b k}(hb:b₁ ≤ b)(h:stationReady Z A b k)(hx:Xhat k=A.clock.hatBeta k):stationReady Z A b₁ k:=by
    have hu:depth b₁ k ≤ depth b k:=by
       unfold Ship.benchCost; apply Nat.add_le_add_right
       change ⌈_ / _⌉₊ ≤ ⌈_ / _⌉₊; apply Nat.ceil_mono; apply div_le_div_of_nonneg_right _ (len_log H ..).2.1.le; apply Real.log_le_log
       · exact mul_pos (Real.rpow_pos_of_pos (exp_pos _) _) (pow_pos (exp_pos _) _)
       apply mul_le_mul_of_nonneg_right _ (sq_nonneg _); exact Real.rpow_le_rpow_of_exponent_le (Real.one_le_exp (sq_nonneg _)) hb
    exact ⟨hu.trans h.1,fun m hm=>h.2 _ ((Nat.sub_le_sub_left hu k).trans hm)⟩

-- price log offset from above: no assertion that logarithm of a field transport has the same bound.
omit H
def LogNear (A:Levels G) (u:ℕ→ℝ):=∃ c:ℝ,0<c ∧ (∀i,0<u i) ∧ ∀ᶠ k in atTop,|Real.log (u k) + A.S.scale k| ≤ c * Real.log (1+A.S.scale k)

include H
lemma stops_near {b₀ b:ℝ}(hG:G.Simple)(h:b₀ ≤ b)(hb: 0 ≤ b₀): LogNear A (gap A b₀ ∘ stopover b A):=by
    let f:=stopover b A
    obtain ⟨C,hC,hB⟩:=depth_width H hG b (hb.trans h)
    refine ⟨2*b₀+C,by linarith only [hC,hb],fun i=> gap_pos ..,?_⟩
    have hF:=hop_large (A:=A) (Z:=Z) b
    have hF:=hF.eventually (prices H hG)
    filter_upwards [hB,hF,(seam_late (A:=A)).eventually_gt_atTop 0] with i hz hv hi
    dsimp only [Function.comp_apply]; unfold gap Station.mag
    change |_ + A.S.scale i| ≤ _
    have hx:0 < A.clock.monitor (stopover b A i):=exp_pos _
    rw [Real.log_mul (A.S.a_pos _).ne' (Real.rpow_pos_of_pos hx _).ne', Real.log_rpow hx, Stock.a_log,Real.log_exp]
    let lm k:=log (1+Y k)
    have he(k):Xhat k = A.clock.hatBeta k:=by unfold Ship.preHat; rw [← H.paid.bar]; rfl
    have hm: A.clock.monitor (f i) = Vac.Numbers.P (Xhat (f i)):= (he (f i)).symm ▸ rfl
    have hu(i):f i ≤ i:= by unfold f Hop; split_ifs; rfl; exact (Nat.sub_le ..).trans (seam_early _) -- le_rfl typo
    have hp:lm (f i)≤lm i:= Real.log_le_log (by
       have ht0:0 ≤ Y (f i):=A.S.scale_zero ▸ scales_route A (Nat.zero_le (f i))
       linarith only [ht0]) (add_le_add_right (scales_route A (hu i)) _)
    have h_lam:0 ≤ lm (f i) := (Real.log_pos one_lt_two |>.trans_le ((len_log H (J (f i))).2.2.trans hv.2.1)).le
    have hs: log (A.clock.monitor (f i)) ≤ 2*lm i:=(le_of_eq (congr_arg Real.log hm) |>.trans (Real.log_le_log (exp_pos _) hv.2.2.1)) |>.trans (hv.2.2.2.trans (by linarith only [hp]))
    have ht : Y i - Y (f i) ≤ C*lm i := by
        dsimp only [f,Hop]; split_ifs with hx
        · simp only [sub_self]; exact mul_nonneg hC.le (h_lam.trans hp)
        change Y i-Y (previous A i) ≤ _
        rw [run_len H i _ (J i) ((by simpa only [f,Hop,if_neg hx] using hu i) : (previous A i) ≤ i) ?_] -- hu i not reduced under hx
        · refine (mul_le_mul_of_nonneg_right (?_: (↑(i-previous A i):ℝ) ≤ depth b i) (len_log H (J i)).2.1.le).trans hz
          exact_mod_cast (by unfold previous; have hc:=seam_early (A:=A) i; dsimp only; omega : i-previous A i ≤ depth b i)
        intro m hm he
        have hm : seam i ≤ m := Nat.le_of_not_gt (fun h=> by unfold previous at hm; omega)
        exact le_antisymm (A.fits.mono he) ((seam_stable (A:=A) ..) ▸ A.fits.mono hm)
    have hx : 0 ≤ Real.log (A.clock.monitor (f i)) := by rw [Calendar.monitor,Real.log_exp]; positivity
    refine abs_le.mpr ⟨?_,?_⟩
    · nlinarith only [scales_route A (hu i),h_lam.trans hp,hs,hx,mul_nonneg hx hb,mul_nonneg hb (h_lam.trans hp),mul_nonneg hC.le (h_lam.trans hp)]
    linarith only [ht,mul_le_mul_of_nonneg_right hs hb]
end YM.OPE.Coverage
