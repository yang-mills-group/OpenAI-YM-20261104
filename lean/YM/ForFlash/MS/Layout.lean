import YM.ForFlash.MS.Wide
import YM.FVA2.Arrival.Runtime
import YM.FVA2.Arrival.Landing
import YM.FVA2.Speed.Fast

/-! # Pay trial on polynomial (in inverse spacing, not its log) layouts

Adapts `marches`, `rate` in Arrival/Runtime, with the wider hypotheses of Wide
and sampling along arbitrary investments. `familiar` throughout (no
snapping it anywhere here).
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.FVA2.Arrival.Schedule
open Function Filter Set Finset Metric MeasureTheory Real Lattice
open MS MS.Local.Physical MS.Tide MS.Tide.PeakT MS.Fleet MS.Orbit MS.Vista MS.Vane MS.Tone MS.Rake MS.Land MS.Dial
open XSpace.Cirrus XSpace.Expense Press Change
open scoped Topology ContDiff Classical
variable {n:ℕ} {G:Gauge}
local notation "Z"=> XSpace.Cirrus.Sample n
variable {I:Type} {s:I→Sample n} {l:Filter I} {C c:ℝ} {m:ℕ}

/-- Point conditions including normalization scale after physical removal (but still a test of
  formal regulator arrays in the application). -/
structure FitsWidthForFlash (c C:ℝ)(m:ℕ)(i:XSpace.Cirrus.Sample n) : Prop where
    welcome : welcome i
    gap : ∀ (u v:Fin n), u≠v → c ≤ ‖plot (familiar i) u-plot (familiar i) v‖
    extent : ∀ u:Fin n, ‖plot (familiar i) u‖ ≤ C * (i.F.spacing)⁻¹ ^ m

variable (μ:ℝ)(C₁:0≤C)(c₁:0<c)(h:Stretched l (grab∘s))
    (p:∀ i,FitsWidthForFlash c C m (s i))(q:∀ i,Sized (s i))
private def setting (s:I→ Z) : MS.Dial.Trial I (Fin n) where
 profile:=⟨ fun i=>theta (s i).F,fun i=> μ-theta (s i).F, fun i=>(showR μ).profile.room (s i) ⟩
 head := (showR μ).head ∘ s
 side := (showR μ).side ∘ s
 off i := (showR μ).off i ∘ s

local notation "P"=> setting μ s
local notation "δ"=> a (grab∘s)
local notation "Y₀"=> (fun i=>theta (s i).F)

include C₁ c₁ p q h
set_option maxHeartbeats 400000 in
private lemma layout : UsesForFlash (setting μ s) l μ :=by
 have he (i:I): δ i = exp (-Y₀ i) := (bornS (q i).unit).symm
 have hs (i:I): 1 ≤ exp (Y₀ i) := Real.one_le_exp ((P).profile.room i)
 refine ⟨ ?_,?_,fun i=>rfl, ?_,?_,fun i=> cleared (s i) (q i), Vista.centered_size _ _ fun i=> (bar_lift (s i) (q i)).symm ⟩
 · intro u
   refine ⟨ C+1,by positivity,m+1,fun i=>?_⟩
   let α:=plot (familiar (s i)) u; let β:=testP P i u; let x:=Tone.embed ((P).off u i); let U:= exp (Y₀ i)
   have hx: U⁻¹ * ‖x‖= ‖β‖:= by change U⁻¹*_= ‖exp (-Y₀ i) • x‖; rw [exp_neg,norm_smul_of_nonneg (inv_nonneg.mpr (exp_pos _).le)]
   have hg := exp_pos (Y₀ i); have h':= hs i
   have hα : ‖α‖ ≤ C* U^m:=by
      have hv : ‖α‖≤ C*(δ i)⁻¹^m:= (p i).extent u
      rwa [he, exp_neg,inv_inv] at hv
   have hβ: ‖β-α‖ ≤ 1:= (approaches (s i) μ u (q i).unit).trans (q i).unit
   change ‖x‖ ≤ (C+1)*U^(m+1)
   have hz: ‖x‖ ≤ U*((C+1)*U^m):=( inv_mul_le_iff₀ hg ).mp (by
      rw [hx]
      rw [ show β= β-α+α from (sub_add_cancel ..).symm ]
      exact (norm_add_le ..).trans ((add_le_add (hβ.trans (one_le_pow₀ h')) hα).trans_eq (by ring)))
   refine hz.trans_eq ?_; ring
 · apply unposeForFlash (v:=μ)
   intro u v huv; refine ⟨ c,c₁,fun i=>?_⟩; change c*exp 0 ≤ ‖testP (showR μ) (s i) u - testP (showR μ) (s i) v‖
   rw [exp_zero,mul_one,planes (s i) μ u (q i).unit,planes (s i) μ v (q i).unit,add_sub_add_right_eq_sub]; exact (p i).gap u v huv
 · have h₀:Tendsto (fun i=> Real.log (δ i)) l atBot:= Real.tendsto_log_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.mpr ⟨h.endpt, Eventually.of_forall fun i=>(s i).F.positive⟩)
   exact (tendsto_neg_atBot_atTop.comp h₀).congr fun i=> (theta_value (q i).unit).symm
 intro u; let k:=⌈u⌉₊; filter_upwards [(h.pay k).eventually_ge_atTop 1] with i hp
 let y:=tickA (P).side i
 have ht' : 1 ≤ (δ i)^k*y := by unfold y tickA; change (1:ℝ) ≤ _*(( (periodN (psi (s i).F)).val : ℕ):ℝ); rw [psi_back]; exact hp
 change u*Y₀ i ≤ log y; apply le_trans (mul_le_mul_of_nonneg_right ( Nat.le_ceil u ) ((P).profile.room i)); rw [← Real.exp_le_exp,Real.exp_log (δ_p ..)]; rw [he,Real.exp_neg,inv_pow, ← Real.exp_nat_mul] at ht'; obtain H: exp ((k:ℝ)*Y₀ i)*1 ≤ y:= (le_inv_mul_iff₀ (by positivity)).mp ht'; rw [mul_one] at H; exact H

variable (Y:XSpace.Initialize G)(u:Fin n→Label (Press.portDeck G)){K:Booked (Press.portDeck G)} (S:MS_Data G K)(M: Land.Prescription (Press.portDeck G)) (g:G.Simple)(ps: TaylorOKF S (Press.wickInput Y) M)
local notation "E"=> entries μ Y u M
local notation "D"=> Landing.moondye μ S u
open Speed
include g ps
set_option maxHeartbeats 400000 in
private lemma sharpLayout (t:Finset (Fin n))(k:ℕ): Sharp l (grab ∘ s) (entries μ Y u M t k ∘ s) (fun i=>Landing.moondye μ S u t k (familiar (s i))) :=by
 let Hl:= layout μ C₁ c₁ h p q
 obtain ⟨V,hV⟩:= check_tFForFlash S ( wickInput Y ) u P ps Hl g true
 have hv (i:I) : fare ( Label.h ∘ u ) (P).profile ( ordZ V ) t k i=E t k ( s i ) := by
    let L:=s i; let N:=psi L.F
    have hL: bury i t V=Top.value Y u M (bar L) (σ L) (periodN N) (μ-theta L.F) t := (Top.identifies Y u M (bar L) (σ L) (periodN N) (μ-theta L.F) t (⟨N.val,two_mul (α:=ℕ) N.val⟩)).1 (hV.cost i t);
    change higher (showR μ).profile ( Label.h ∘ u |> fun g=>charge g t ) L * _= ((L.F.spacing:ℂ)^_)⁻¹*_
    rw [show ordZ V t k i = _ from congr_fun hL k, wholeAt Y u M t (μ-theta L.F) (periodN N) _ _ L (offset L), psi_back L.F, meter μ u t (q i)]
 have HH : twin l (P).profile mildG (entries μ Y u M t k ∘ s) (fun i=>Landing.moondye μ S u t k (familiar (s i))) := by
    have H (i:I): tour S u μ ( testP P i ) = tour S u μ (plot (familiar (s i))) :=by
       unfold tour; rw [show book S u μ (testP P i)= _ from (?_ : book S u μ (testP P i)=book S u μ (plot (familiar (s i))))]; exact Dposition μ u S (s i) (q i) (microForFlash P Hl.knit i)
    rw [← (show fare ( Label.h ∘ u ) (P).profile ( ordZ V ) t k=E t k ∘ s from funext hv),
        ← show (fun i=>tour S u μ (testP P i) t k)=(fun i=> Landing.moondye μ S u t k (familiar (s i))) from funext fun i=> congr_fun (congr_fun (H i) t) k]
    exact hV.bouquet t k
 obtain ⟨⟨r,hr,hq⟩,d,_,hd⟩:= HH
 refine ⟨XSpace.Expense.Cap.of_bounds r ?_, Fast.put d ?_⟩
 · filter_upwards [ hq ] with i hi; unfold lake at hi; simpa using hi
 filter_upwards [ hd ] with i hi; refine hi.trans_eq ?_; unfold lake Speed.chip; rw [show (P).profile.θ i=-Real.log (δ i) from theta_value (q i).unit,Real.rpow_def_of_pos (((grab∘s) i).positive)]; congr 2; change -mildG * -log (δ i) = log (δ i)*mildG; ring

omit p q in
/-- Raw ordinary regulator coefficients, linked period-to-spacing, polynomial layout. -/
theorem sharpForFlash (A:∀ᶠ i in l, FitsWidthForFlash c C m (s i))
    (t:Finset (Fin n))(k:ℕ): Sharp l (grab ∘ s) (entries μ Y u M t k ∘ s) (fun i=>Landing.moondye μ S u t k (familiar (s i))) :=by
  rcases l.eq_or_neBot with eq|ne
  · subst l; exact ⟨XSpace.Expense.Cap.of_bounds 1 (by simp), Fast.put 1 (by simp)⟩
  have H:∀ᶠ i in l,FitsWidthForFlash c C m (s i)∧ Sized (s i):= by
     filter_upwards [A,h.smaller,h.horizon.eventually (eventually_ge_atTop 16)] with i hi ht hw
     exact ⟨hi, Nat.cast_le.mp (show ((16:ℕ):ℝ)≤(((s i).F.p.side.val:ℕ):ℝ) from (by exact_mod_cast (show (16:ℝ) ≤ ↑(s i).F.p.side.val from hw))), ht,hi.welcome⟩
  obtain ⟨i₀,hi⟩:= H.exists
  let y i:= if FitsWidthForFlash c C m (s i)∧ Sized (s i) then s i else s i₀
  have B₀ i: FitsWidthForFlash c C m (y i)∧ Sized (y i):=by unfold y; split; assumption; exact hi
  have hx: s=ᶠ[l]y:= H.mono fun i hi=> (if_pos hi).symm
  have hx':(grab ∘ s)=ᶠ[l] (grab ∘ y):= hx.fun_comp grab
  have hh:Stretched l (grab∘y):= 
     frontier.wider ( ( goesFront h ).congr' hx' )
  have hy:= sharpLayout μ C₁ c₁ hh (fun i=> (B₀ i).1) (fun i=> (B₀ i).2) Y u S M g ps t k
  let A':I→ℂ:= fun i=>Landing.moondye μ S u t k (familiar (y i))
  have hu : Sharp l (grab∘s) (entries μ Y u M t k ∘ y) A':= ⟨hy.quote, Asymptotics.IsBigO.congr' hy.sails (.refl ..) (show (fine (grab∘y)) =ᶠ[l] (fine (grab∘s)) from hx'.symm.fun_comp chip)⟩
  exact hu.tee (hx.symm.fun_comp (E t k)) (hx.symm.fun_comp (D t k ∘ familiar))

end YM.FVA2.Arrival.Schedule
end
