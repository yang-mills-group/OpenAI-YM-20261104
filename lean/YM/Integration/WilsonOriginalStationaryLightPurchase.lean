import YM.Integration.WilsonOriginalStationaryLightPath

set_option autoImplicit false
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Supply
open scoped Topology ContDiff BigOperators
variable {G: Gauge} {s: Sheet G}{L : Rolls s} {Θ : Protection L}{a:Levels G}{Z: ChartRatio G}
variable {w: Delays Θ} {y: Bar w}{v:Wait y}{V: Horizon a}{Q:PostCost L}
theorem verdantWithLight (cap : ℝ → ℝ) (movable : Movable cap) (G : Gauge) (hS : G.Simple) (B : MapPrices) (K : KernelChoices) (B₀ : ℕ→ℝ) (he : ∀ i, 0 ≤ B₀ i) (h : Fluent G) :
    ∃ σ A : ℕ→ℝ,(∀ i,0<σ i) ∧ (∀ i,0≤A i) ∧ ∀ (τ A' : ℕ→ℝ),τ ≤ σ → (∀ i,0<τ i) → A ≤ A' →
    ∃ (d γ : ℕ→ℝ) (u : ℕ→ℕ),(∀ i, 0≤d i) ∧ (∀ i,0<γ i) ∧ ∀ (s : Sheet G), s.kernel=K → Buys s τ A' d u B₀ →
      ∀ (L : Rolls s),∃ (V : ℕ →ℕ) (η : ℕ→ℝ), BudgetGap s L B η ∧ ∀ (Θ : Protection L),
        ∃ Δ : ℕ→ℝ, ∀ (D : Delays Θ) (T : Bar D) (M : Wait T), Δ≤D.betaEntry → V ≤ D.shells → ∀ (Q : PostCost L),Q.η=η → 1≤Q.Γ → Q.c ≤ γ →
        ∀ a : Levels G,Paid M a → ∀ X W : Horizon a, Craft.Rack a B X → Bid.Retained W X →
          ∀ Y : ChartRatio G,LocalRatio Y → ∃ (T':ℕ→ Reel G), MailBox (A:=a) (Z:=Y) W Q T' ∧ ∃ U : Kin W Y, Inspected U Q T' ∧ LightPath U cap := by
  obtain ⟨σ,A,hσ,hA,H,Q',hQ0,P⟩ := mastering G hS K B B₀ he
  let v i:=min (σ i) ((B.α i)/2)
  refine ⟨v,A,fun i=>lt_min (hσ i) (half_pos (B.alpha_pos i)),hA,fun τ A' ht hv hw => ?_⟩
  obtain ⟨d,y,u,F,W,h1,Lh⟩ := P τ (fun i=> A' i*64) hv (fun i=>mul_nonneg ((hA _).trans (hw _)) (by norm_num)) h
  refine ⟨d,fun i=> y i/2,u,fun i=>(h1 i).1,fun i=> half_pos (h1 i).2,fun s hs hB L => ?_⟩
  obtain ⟨η,H'⟩ := scene_gate L B
  choose V hT using fun i => waits_up (F i (L.L i)) (y i) 1 (h1 i).2 zero_lt_one
  refine ⟨fun i=> max (GateVolume i) (V i),η,H',fun Θ=> ?_⟩
  obtain ⟨Δ,hΔ⟩ := clocks G hS s L Θ (fun i=> W i (L.L i))
  obtain ⟨Δc,hΔc⟩ := summerClocks cap movable G hS s L Θ (fun i=> W i (L.L i))
  refine ⟨Δ ⊔ Δc,fun w β b he hl Q hη hg hc a hd X Y hx hy Z HZ => ?_⟩
  have hw₀ := hΔ w β b (le_sup_left.trans he) a hd
  have small₀ := hΔc w β b (le_sup_right.trans he) a hd
  have hpW i : (s.profile i).width ≤ σ i := (hB.fields i).1.trans_le ((ht i).trans (min_le_left ..))
  have hk i : A i ≤ (s.profile i).paths := (hw i).trans_eq (hB.fields i).2.symm
  have hg' i (n : Side) (hL': w.shells i ≤ n.val) : F i (L.L i) * Real.exp (-(y i)*n.val) ≤ Q.Γ i*Real.exp (-(Q.c i)*n.val) := by
    have hh : Q.c i ≤ y i/2 := hc i
    have hξ : 1≤Q.Γ i := hg i
    refine (hT i n ((le_max_right ..).trans ((hl i).trans hL'))).trans (mul_le_mul hξ (Real.exp_monotone (by gcongr)) (Real.exp_pos _).le (zero_le_one.trans hξ))
  let t i:=Q' (a.clock.J (i+1)) (a.clock.J i)
  have hM:MailBox Y Q t (Z:=Z):=by
     refine ⟨fun i=> (hw₀ i).2.2,fun i=> ?_, fun i p=> larger hd (fun i=> (le_max_left ..).trans (hl i)) i p,?_,?_⟩
     · have hy:=(hpW (a.clock.J i))
       have he :(a.params i)=s.profile (a.clock.J i) := by unfold Levels.params Calendar.params; rw [hd.stage]
       let k:= a.clock.J (i+1); let j:=a.clock.J i; have hm: k=j ∨ k=j+1:=by have h:j≤k:=a.fits.mono (Nat.le_succ _); have hh:k≤j+1:=a.fits.stepSlow _; omega
       rw [he]; have h:= hQ0 _ _ hm; exact ⟨lt_of_le_of_lt hy h.1,lt_of_le_of_lt hy h.2.1,lt_of_le_of_lt hy h.2.2⟩
     · intro i; let j:= a.clock.J i; refine ⟨B.α j,B.Ω j,?_, (eventually_gt_atTop i).mono fun n hn =>?_⟩
       · unfold Levels.params Calendar.params; rw [hd.stage]; exact lt_of_le_of_lt ((hB.fields j).1.le.trans ((ht j).trans (min_le_right ..))) (half_lt_self (B.alpha_pos _))
       rw [hy.1]; exact (hx.covers _ _ hn.le).2.2.2.1
     intro m N hN R hR hi
     unfold haloB at hR
     refine florentine hd (hη.symm ▸ H') (fun i=> le_trans (le_max_left ..) (hl i)) hg' hB.axis hpW hk hB.gradient hB.days HZ hx hy ?_ hw₀ hR hi hN
     rw [hs]; rw [funext fun i=> (hB.fields i).1,show (fun i=>(s.profile i).paths*64)=(fun i=> A' i*64) from funext (fun i=> by rw [(hB.fields i).2])]; exact Lh
  refine ⟨t, hM, ?_⟩
  refine settledWithLight cap t hd hM.step
    (fun N => bard cap hd hpW hk hB.axis hx hy H (fun i => (small₀ i).2.2) N) ?_
  intro m N hm R hr
  refine florentineLight hd (hη.symm ▸ H') (fun i => le_trans (le_max_left ..) (hl i)) hg'
    hB.axis hpW hk hB.gradient hB.days HZ hx hy ?_ cap small₀ hr.2 hr.1.ties hm
  rw [hs]
  rw [funext fun i=> (hB.fields i).1, show (fun i => (s.profile i).paths*64) = (fun i => A' i*64)
    from funext (fun i => by rw [(hB.fields i).2])]
  exact Lh

end YM.Stationary
end
