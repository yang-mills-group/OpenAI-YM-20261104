import YM.MS.ScaleForest.Parking
import YM.MS.ScaleForest.Frontier
/-!
# Budgets for all input grades, including single-pin prepared and quotient terms

Supplies a single master statement. Need SOME paid exponent for working
with an isolated polar part; use one common n along the whole subhistory.
Later use `Frontier.enter` to take other limits in the file's prescription.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum
open Detect Tone Momentum Osc Fiddle Metric
open scoped Topology ContDiff
variable {G : Gauge} {I J : Type} [TopologicalSpace I] {X Y : Curtain G I} {R T a b : ℝ} {p : ℤ} {Z:ℂ} {F V: Flats G}{n k m h : ℕ}{g:Bool}

omit [TopologicalSpace I] in
-- Iris invariance over pages
theorem sameStation (hp:Pact F V)(μ:ℝ)(t:ℕ): Iris (I:=I) (startPaid μ t F) (startPaid μ t V):= by
   filter_upwards [took hp] with i hi; funext s x; have he := Train.treaty i hi t μ s; rw [ ← starter F μ t t i s x, ← starter V μ t t i s x] at he; obtain h:= congr_arg (plow ((t:ℂ)-t) (-s)) he; unfold backing at h; rwa [ snow,snow,neg_add_cancel,posing,posing ] at h

-- stationary curves for weight zero movers with no later attachment
variable {H:Mob G} {W : GraphSum G g 0}
private def glisten (H:Mob G) (n:ℕ): Curtain G I:= fun z _ _=> z^n • H
private lemma Gemstone (he : Form0 false H) (hp : Goods 0 H)(ht:Goods p H) (n:ℕ) : let F:Curtain G I:=glisten H n; Waves R p F ∧ Frontier F ∧ Paces F p:= by
   let Y:Curtain G I:=glisten H n; intro K
   have hx (R:ℝ): Waves R p Y:= {
      sway := fun m w=> by
         change Continuous (fun i:Atlas I R=> (i.1.val ^ n) * H m w); fun_prop
      hol := fun i _=> (Hol.stays he.price).rate (x:=fun z:ℂ=>z^n) (fun _ _=>by fun_prop)
      token := fun _ _ _ _=> Sturdy_scale he.token _
      funds := fun z _ _ _=> (good ..).smul_mem (z^n) ht }
   refine ⟨ hx R,fun b h hb=>?_ ,fun b h hb=>?_ ⟩
   · refine ⟨ _,Enough.simple,⟨ fun m=>?_ ⟩ ⟩;
     refine ⟨ fun z (_:I)=> z^n • H m [], fun _ _ _=> by fun_prop, ?_ ,1,zero_lt_one,fun z hz i s h=>?_ ⟩;
     · exact Continuous.mul (by fun_prop) continuous_const
     change ‖(z^n) • H m []-(z^n) • H m []‖≤_; rw [sub_self,norm_zero]; positivity
   let R:ℝ:= 1/4; refine ⟨ R,Enough.simple,hx R,0,?_ ⟩; by_cases hz:p=0
   · unfold vcost; rw [if_pos hz]
     intro J z s v; unfold OnTest; simp_rw [show ∀ i:ℝ, levy 0 0 i=1 from fun i=>by unfold levy; split <;> simp]; 
     have hv : scaleC 0 1 (fun i=> ‖(z i).val^n‖):= by
       exact ⟨ 1,zero_lt_one,0, fun i p he=> (by simp only [norm_pow,pow_zero,Pi.one_apply,mul_one]; refine pow_le_one₀ (norm_nonneg _) ((Enough.simple.norm (z i).property).trans (by norm_num)))⟩
     convert! fall_scale (travel he.price) (z:=(0:J→ℝ)) (U:=fun i=> (z i).val^n) (b:=1) hv using 1 ; first | rfl | simp
   apply vacant
   have h : H=0:= by
      funext m l; by_cases hu: (l.length:ℤ)=0; exact ranks_off ht l (by omega); exact ranks_off hp l hu
   unfold Slipped probe K glisten; rw [h]; simp_rw [smul_zero]; rfl

omit [TopologicalSpace I] in
private lemma glide (hp:Pact F (collapsed (fun _=>H)))(μ:ℝ) : Iris (I:=I) (taper n (startPaid μ 0 F)) (glisten H n):= by
   apply (EventuallyEq.trans (utaper (sameStation (I:=I) hp μ 0) n)); refine Eventually.of_forall fun z=>?_; funext t x; change z^n • startPaid _ 0 (collapsed (fun _=>H)) z t x = _; let B:= collapsed (fun (_:ℂ)=>H); have h: startPaid μ 0 B z t x=H := by
      obtain he:= congr_arg (plow 0 (-t)) (starter B μ 0 0 z t x); rw [page_sl] at he; unfold backing at he; simpa [ew, cubic, gNat, snow] using he
   rw [h]; rfl

-- applying to raw Page lift weights

theorem staticLife (hp:parked p F)(μ:ℝ)(n:ℕ) : let X : Curtain G I:= populated (taper n (startPaid μ 0 F));
    Frontier X ∧ Paces X p := by
   obtain ⟨H,he,h,hP,hV⟩:=hp; intro X; obtain ⟨hW,H,T⟩:= Gemstone (R:=1/4) (I:=I) he h hP n
   have hp:= colonize hW Enough.simple (EventuallyEq.symm (glide (n:=n) hV μ)); exact ⟨ H.congr hp,T.congr hp⟩

-- positive height source exterior

theorem kitPlusPace (hx:Kit a p X)(ha:1 ≤ a): Paces X p:= by intro b hb hp; obtain ⟨ R,hR,hW,hT⟩:= hx (a-b) (by linarith); exact ⟨ R,hR,hW,-a-(a-b), hT.relax le_rfl ((vcost_le hb p).trans (le_of_eq (by ring)))⟩
theorem kitPlusLimit (hx:Kit a p X)(ha:1 ≤ a): Frontier X := by
   intro b hb hp; obtain ⟨R,hR,hW,hP⟩:= hx (a-b) (by linarith); rw [sub_sub_self] at hP; refine ⟨ R,hR,⟨ fun m=>?_ ⟩ ⟩
   obtain ⟨C,hC,hU⟩:= priceScalar m hP; exact ⟨ (0:ℂ→I→ℂ), fun _ _ _=> differentiableAt_const _, continuous_const, C,hC,fun z hz i s ht=> (by simpa only [Pi.zero_apply, sub_zero, ilev _ _ ht] using hU (⟨z,hz⟩:disc R) i s)⟩
lemma basicKit (h:Kit 0 p X): Hover X p:= by unfold Hover; intro b hb; simpa only [neg_zero, zero_sub] using h b hb

lemma tenure (hp:h=0→parked p F) (ht:Moony g F) (hm:OfRank p F)(hV:Rent F n)(μ:ℝ) : let X: Curtain G I:= populated (taper n (startPaid μ h F)); (Frontier X ∧ Paces X p) := by
   by_cases hh:h=0; · subst h; exact staticLife (hp rfl) μ n
   obtain hc:= compensated (I:=I) h μ ht hm hV; have hH:1≤(h:ℝ):= by exact_mod_cast (show 1≤h by omega)
   exact ⟨ kitPlusLimit hc hH,kitPlusPace hc hH⟩

lemma equity (hp:h=0→parked p F) (ht:Moony g F) (hm:OfRank p F)(hs:Stay h F)(μ:ℝ):
    Frontier (I:=I) (asLeaf F μ h) ∧ Paces (I:=I) (asLeaf F μ h) p := by
   unfold asLeaf; by_cases hh:h=0
   · subst h; obtain H := staticLife (I:=I) (hp rfl) μ 0; rw [ show taper 0 (startPaid μ 0 F)=(startPaid μ 0 F:Curtain G I) from funext fun z=> by rw [taper,pow_zero,one_smul]] at H; exact H
   obtain hc:= compensated_free (I:=I) h h μ ht hm hs; have hH :1≤(h:ℝ):= by exact_mod_cast (show 1≤h by omega)
   exact ⟨ kitPlusLimit hc hH,kitPlusPace hc hH⟩

lemma occupancy (X:GraphSum G false h) (μ:ℝ) : let V: Curtain G I:= asLeaf X.instructions.renorm μ h
      Frontier V ∧ Paces V X.slots := equity (fun h=> (Vacancy X h).1) (clockMoon X.accepted.usable.clock) X.accepted.after_rank X.accepted.after.toll μ
lemma tires {X:GraphSum G false h} (hT:F∈ X.quotients)(μ:ℝ): ∃ n, let V:Curtain G I:= populated (taper n (startPaid μ h F));
      Frontier V ∧ Paces V X.slots := by
   obtain h:= clockMoon ((X.quotient_valid F hT).choose_spec.clock); exact ⟨ _,tenure (fun p=>(Vacancy X p).2 F hT) h (quotientRank X F hT) (sufficientBound ( Moony.toast h)) μ⟩
lemma resetBulk (X:GraphSum G true 4)(μ:ℝ) : Hover (I:=I) (asLeaf X.instructions.renorm μ 0) X.slots := by
   obtain H:= X.accepted; exact basicKit (by simpa only [Nat.cast_zero,asLeaf] using compensated_free (I:=I) 0 4 μ (clockMoon H.usable.clock) H.after_rank H.after.toll)
lemma tiBulk {X:GraphSum G true 4} (hT:F∈X.quotients)(μ:ℝ): ∃ n, Hover (I:=I) (populated (taper n (startPaid μ 0 F))) X.slots := by
   obtain h:= clockMoon ((X.quotient_valid F hT).choose_spec.clock); obtain ht := compensated (I:=I) 0 μ h (quotientRank X F hT) (sufficientBound (Moony.toast h)); rw [Nat.cast_zero] at ht; exact ⟨ _, basicKit ht ⟩
end YM.MS.ScaleForest
