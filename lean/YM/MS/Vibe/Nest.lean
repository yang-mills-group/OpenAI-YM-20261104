import YM.MS.Vibe.Escape
/-!
# Rank clean via mask lemmas and net. Ghost mark charges unconstrained momenta.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Emit
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color _root_.YM.MS.Shine Hem Mell Logarithm Pearl Train Dock
open Signal Book Convolve Garment.Wave Garment.Wick
open scoped Topology ContDiff Interval
variable {I:Type} {G:Gauge}{Z K F:Mob G} {u v w:T (Mob G)}{X Y:T (Flats G)}{D:Rip G}{J N:Flats G}{f g:Coat G}{t r:ℤ}{a h n m k ℓ:ℕ}{i:ℂ} {s y:ℝ}{b c:Bool}
def CleanP (b:Bool)(J:Flats G): Prop:=∀ᶠ i in dotty, ∀ n, Equal b (J n i) 0
lemma level (h:∀ n,zeroTest b (J n i) r)(k:ℕ): zeroTest b (Parade J k y s i) r := ⟨fun m l hm hC=>by unfold Parade Finsupp.sum; simp only [Finset.sum_apply]; refine Finset.sum_eq_zero fun p hp=>?_ ; unfold hikeP; simp only [Pi.smul_apply,plow,(h p).passes m (sr s l) (by unfold sr; simpa using hm) (fun hx=>by rw [net_sr,hC hx,smul_zero]),mul_zero,smul_zero]⟩ -- check hC binder
lemma orbit (h:∀ n, Equal b ( J n i) 0)(k:ℕ): Equal b ( Parade J k y s i) 0:= fun m l hm=> ( level (fun i=> ⟨ fun m w _ hw=>h i m w hw⟩) k (r:=l.length) (s:=s) (y:=y)).passes m l rfl hm
lemma spot_pr (hp:i∈Town)(hF: Form0 false K)(he: zeroTest b K (r+2)): zeroTest b (( Grid i y s G).P K) r:= by
    let V := Grid i y s G; have hA:= (A_caps G s).clearer; change zeroTest _ (unitC i y _ K) _; rw [unitC,LinearMap.smul_apply,port_spec hp _ hA hF]; exact ⟨ fun m l hx hc=> by simp only [Pi.smul_apply,(roof_ocean hF hA he hp).passes m l hx hc,smul_zero]⟩
-- arbor orientation heavy. directly use Heat.tres.EqOn
lemma tree_star (hp:Equal b K 0): Equal b ( squad D F K) 0:= by
    cases b; · rw [IdEq hp,map_zero]; exact fun _ _ _=>rfl
    have ht : Equal true (arbor D F K) (arbor D F 0):= by intro m l hl; exact agrees_tree ( F m) (K m) ( X:=D m) (p:=Landau.parity) (fun _ _=>rfl) (fun w hw=> hp m w (fun _=>hw)) l (hl rfl)
    rw [← schedule,← schedule D F 0,map_zero] at ht; exact ht
lemma tree_cast (hp: Equal true K 0) : squad D K F=0:= by
    suffices h:arbor D K F=arbor D 0 F by rw [← schedule D 0 F,map_zero,LinearMap.zero_apply,← schedule] at h; exact h
    unfold arbor; funext m; exact tree_agrees _ _ (K m) _ _ (fun i hi=> hp m i (fun _=>hi))
lemma noLives (hp:i∈Town)(h: u 0=0)(hm:∀ i<n,Equal b (v i) 0) (hf:Form0 false (v n))(he:zeroTest b (v n) (r+2)): zeroTest b ((Grid i y s G).lives u v n) r := by
   let V:= Grid i y s G; have ht: Equal b (pairW V.X u v n) 0:= by
       intro m l hC; rw [paired, Finset.sum_apply, Finset.sum_apply]; refine Finset.sum_eq_zero fun i hi=>?_ ; by_cases hI:i.1=0; · rw [hI,h,map_zero]; rfl
       obtain hx:=Finset.mem_antidiagonal.mp hi; exact tree_star ( D:=A0 G s) (hm i.2 (by omega)) m l hC
   constructor; intro m l hL hC; unfold GridR.lives; rw [Pi.add_apply, Pi.add_apply,Pi.add_apply,ht m l hC,promised,(spot_pr hp hf he).passes m l hL hC]; exact add_zero ..
lemma noExtra (hp:∀ i≤ n, Equal true (u i) 0): pairW (squad D) u v n=0:=by rw [paired]; refine Finset.sum_eq_zero fun i hi=>tree_cast ?_; exact hp i.1 (by obtain hx:=Finset.mem_antidiagonal.mp hi; omega)
-- combine Rank turn.U.
def Guard (F:Flats G)(h:ℕ)(b:Bool): Prop:= ∀ r:ℤ, Blink b F (r+2) → Calm h b F r
structure FallM (V:Flats G)(b:Bool)(r:ℤ): Prop where
    body :∀ᶠ i in dotty,∀ k,∀ t>r,zeroTest b ( V k i) t
lemma full (hp:Host J h)(ht: Return J f h)(hx:Scorched f b)(he: Guard J h b): CleanP b J ∧ Clean f b:= by
    have hf(k:ℤ)(hl:FallM J b k): Calm h b J k:= he k ( hl.body.mono fun i hi n=> hi n (k+2) (by omega))
    have hV(k:ℤ)(h:FallM J b k): FallM J b (k-1):= by
       have hz:= beyond hp ht hx (hf k h); constructor; filter_upwards [ hz, h.body] with i hi h n s hy; by_cases hx:s≤k; · rw [show s=k by omega]; exact hi n
       exact h n _ (by omega)
    have hu: CleanP b J:= by
       obtain ⟨r,hr⟩:= hp.cap; have h(n:ℕ): FallM J b (r-n):= by induction n with| zero=> push_cast; rw [sub_zero]; exact ⟨ (facade (G:=G) J (fun _ _ F=>Issue r F) id dotty (fun _ _=>(grade r G).zero_mem) (fun i=>hr i)).mono fun i hi j t ht=> issue_pl (hi j) ht ⟩| succ n ih=> convert hV _ ih using 1; omega
       obtain hh: r-(↑(r.toNat+1):ℤ)<0 := by omega
       refine (h (r.toNat+1)).body.mono fun i hi n m l hp=>?_ ; exact (hi n (l.length:ℤ) (by omega)).passes m l rfl hp
    exact ⟨hu,fun i m l hl=> ( zeroTest_of_calm_return hp ht hx ( he l.length (Eventually.mono hu (fun i hi n=>⟨fun m w hw hp=>hi n m w hp⟩ ))) i).passes m l rfl hl⟩
end YM.MS.Emit
