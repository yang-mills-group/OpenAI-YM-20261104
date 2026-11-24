import YM.Next.STATIONARY.FullPlanned
/-!
# A slowly growing bound for the loops along one path

`Movable f` gives growth, an eventual bound for each nonnegative additive
shift, and an upper bound relative to the clock monitor. `summerClocks`
uses these properties to place `f (a.clock.hatBeta m)` below the full
loop cap and above the requested bound at each level. With the purchases
and the local ratio in its hypotheses, `under_light` gives one `Kin`
satisfying both `FullPaths` and `LightPath`.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Supply
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {s : Sheet G} {L : Rolls s} {Θ : Protection L} {a : Levels G}
    {P : MapPrices} {K V : Horizon a} {Z : ChartRatio G} {W : Delays Θ} {y : Bar W} {w : Wait y} {Q : PostCost L}
open Asymptotics
structure Movable (f:ℝ→ℝ) :Prop where
   grows : Tendsto f atTop atTop
   relaxes (c:ℝ) : 0 ≤ c → ∀ᶠ x:ℝ in atTop, f (x+c)/2 ≤ f x
   cap (Θ:ℝ) : 0<Θ → ∀ᶠ x:ℝ in atTop, f x ≤ 2 * (Real.exp ((Real.log (Real.log x))^2)) ^ Θ
section light
variable (f:ℝ→ℝ)(g:Movable f)
local notation "T0" a:max m:max=> f ((a).clock.hatBeta m)


include g in
lemma summerClocks (G : Gauge) (h : G.Simple) (s : Sheet G) (L : Rolls s) (Θ : Protection L) (M : ℕ → ℝ) :
    ∃ Δ : ℕ → ℝ, ∀ (D : Delays Θ) (T : Bar D) (V : Wait T), Δ≤ D.betaEntry → ∀ a : Levels G,Paid V a → ∀ m,
     let j := a.clock.J (m+1); M j ≤ T0 a m ∧ T0 a (m+1)/2 ≤ T0 a m ∧ 1 ≤ T0 a m ∧ T0 a m ≤ a.clock.loopCap m := by
  let v i := G.slopeConstant * Real.log (L.L i).val
  have hv i : 0 ≤ v i := mul_nonneg (Gauge.slopeConstant_pos h).le (Real.log_nonneg (by exact_mod_cast Nat.succ_le_iff.mpr (L.L i).pos))
  choose w hw using fun i => eventually_atTop.1 (((g.grows.eventually_ge_atTop (M i)).and (g.relaxes (v i) (hv i))).and ((g.grows.eventually_ge_atTop 1).and (g.cap _ (Θ.pos i))))
  refine ⟨w,fun D T V hp a H m => ?_⟩
  let s := a.clock.hatBeta m; intro j
  obtain ⟨⟨ht,hk⟩,hr,hf⟩ := hw j s ((hp j).trans (H.pays _))
  let E:= a.clock
  have hθ : E.theta j=Θ.theta j := congr_fun H.theta j
  have hx : a.clock.theta j≤ a.clock.theta (a.clock.J m) := a.fits.thetaMono (a.fits.mono (Nat.le_succ _))
  have hm : (1:ℝ) ≤ a.clock.monitor m := Real.one_le_exp (by apply sq_nonneg)
  have hL : (a.clock.monitor m)^(Θ.theta j)≤ (a.clock.monitor m)^(a.clock.theta (a.clock.J m)) := Real.rpow_le_rpow_of_exponent_le hm (hθ ▸ hx)
  have he : s+v j=a.clock.hatBeta (m+1) := by
    have hf : (L.L j)=a.clock.schedule.block m := (congr_fun H.lengths _).symm.trans (a.fits.sameFactor _)
    unfold s v; rw [hf,Calendar.hatBeta, Calendar.hatBeta, Schedule.scale_succ]; ring
  exact ⟨ht,he ▸ hk,hr, hf.trans (mul_le_mul_of_nonneg_left hL (by positivity))⟩

lemma lightUp {R:PathData G}{p:Clip}{a w Λ Λ':ℝ}(H:R.Bounds p a w Λ)(h:Λ≤Λ'): R.Bounds p a w Λ':=by
    refine { H with two:=?_ }; obtain ⟨hp,ht,he⟩:= H.two; exact ⟨hp,ht,he.trans h⟩

def Light (f:ℝ→ℝ) (a: Levels G)(m:ℕ)(R: PathData G):= R.Bounds (a.params m).clip (a.params m).width (a.params m).paths (f (a.clock.hatBeta m))
section level
variable {Zc A σ d g : ℕ → ℝ} {u : ℕ → ℕ} {F T : ℕ → Side → ℝ} {m N : ℕ}
variable (h : Paid w a) (hΘ : BudgetGap s L P Q.η) (hS : ∀ i, GateVolume i ≤ W.shells i) (ht : ∀ i (n : Side),W.shells i ≤ n.val → F i (L.L i)*Real.exp (-(g i)*n.val) ≤ Q.Γ i*Real.exp (-Q.c i*n.val))
variable (hi : (fun i=> (s.profile i).clip.direct) ≤ Zc) (hw : (fun i=> (s.profile i).width) ≤ σ) (hA : A ≤ fun i => (s.profile i).paths)
    (hq : d ≤ fun i => (s.profile i).drift) (hp : u≤ s.floorL) (he : LocalRatio Z)
    (hb : Craft.Rack a P K) (hk : Bid.Retained V K) (hJ : Proceed G P s.kernel Zc σ A (fun i=> (s.profile i).width) (fun i=> (s.profile i).paths) d g u F T)
include h hΘ hS ht hi hw hA hq hp he hb hk hJ
lemma sunny (H : ∀ m,let j := a.clock.J (m+1); T j (L.L j) ≤ T0 a m ∧ T0 a (m+1)/2 ≤ T0 a m ∧ 1 ≤ T0 a m ∧ T0 a m ≤ a.clock.loopCap m) {R : PathData G} (hy : R.Bounds (a.params (m+1)).clip (a.params (m+1)).width (a.params (m+1)).paths (T0 a (m+1))) (hu' : Attached (V.H N (m+1)) R) (hm : m < N) :
    ∃ D α ρ, Light f a m D ∧ Bubble V Q Z N m R D α ρ := by
  let i:= a.clock.J m; let j:= a.clock.J (m+1); let U := a.params (m+1); let T' := a.params m
  let C := a.clock; let M:= (a.clock.op m 0).patch
  let p:= V.towers N m; let b := V.H N m; let z := V.H N (m+1)
  have hj : M.L=L.L j := (a.fits.sameFactor m).symm.trans (congr_fun h.lengths _)
  have h' : j=i ∨ j=i+1 := by
    have h : i≤j := a.fits.mono (Nat.le_succ m); have hi : j≤ i+1 := a.fits.stepSlow m; omega
  have hu : U=s.profile j := by unfold U Levels.params Calendar.params; rw [h.stage]
  have hT : T'=s.profile i := by unfold T' Levels.params Calendar.params; rw [h.stage]
  have hg v := larger h hS m v
  have hF := hull_fact hb hk hm; have hT' := hull_fact hb hk (le_of_lt hm)
  obtain ⟨h2,Ld⟩ := tack_columns hb hk hm
  let f0 :=  fun t => a.S.side m t; let c := fun t=> a.S.side (m+1) t
  have hv t (F : Forest (a.clock.op m t).ratio) := hΘ.ask j (a.clock.op m t) h.kernel hj rfl (hg t) F z b U.clip T'.clip R U.width U.paths _ _ _ _ p (Ld t) (hF.2.2.1 _) hy hu' (hF.2.2.2 t) (hT'.2.2.1 _)
  have hK t F := (hv t F).1
  choose ρ hρ using fun i F=> (hv i F).2
  let fF (t : ℕ) : Forest (a.clock.op m t).ratio := Classical.choice (Tree.select _ M.odd_side)
  let ξ : Armada f0 c M C.kernel := ⟨fun t=> (a.clock.op m t).sizes⟩
  let a' := fun i=> ρ i (fF i)
  have hZ : Transition G C.kernel j (P.η j) (P.α j) (pacesE P j) (Zc j) (P.α i) (pacesE P i) (Zc i) U.paths U.width (A i) (d j) (σ i) (g j) (u j) (F j) (T j) := by rw [hu,show C.kernel=s.kernel from h.kernel]; exact hJ.moon j i h'
  have hΦ : Scud ξ G U.clip T'.clip R fF a' (P.α j) U.width (pacesE P j) U.paths (pacesE P j) (P.η j) (T0 a (m+1)) (P.α i) (pacesE P i) (P.η i) z b p (Q.η j) :=
      ⟨hg, hF,hT',hu',hy,h2,Ld,fun t=> hK t _,fun i=> (hρ i _).1,fun i=>(hρ i _).2.1, fun i=>(hρ i _).2.2⟩
  obtain ⟨Y,α,hX,hY,hP,hE,hG,H'⟩ := hZ f0 c M ξ U.clip T'.clip R fF a' z b p (T0 a (m+1)) (P.η i) (Q.η j) Z rfl (by rw [hj]; exact (hp j).trans (L.large j).need) (bound_climb G a m) (hu ▸ hi j) (hT ▸ hi i) hΦ ((H (m+1)).2.2.1) (Q.price _) he
  obtain ⟨hy',hr,_,hr₀⟩ := H m
  have hSat : Y.Bounds T'.clip T'.width T'.paths (T0 a m) := hP _ _ _ (a.params _).width_pos (hT ▸ hw i) (hT ▸ hA i) (by rw [hj]; exact hy') hr
  refine ⟨Y,α,ρ,hSat, ⟨hE.trans (show d j ≤ U.drift from hu ▸ hq _), ⟨hX,hY, lightUp hSat hr₀⟩,fun t v => ⟨hK t v,(hρ t v).1, (hρ t v).2.1,?_,?_⟩⟩⟩
  · exact Bid.one_for_all (a.clock.op m t) Work.F05.answer (hg t) (fF t) U.clip T'.clip R Y U.width U.paths _ _ (Q.price _) hy Z he (ρ t) (fun F=> (hρ t F).1) (hK t) (hG t) v
  have hn : W.shells j ≤ (f0 t).val := (Nat.le_mul_of_pos_right _ (by positivity)).trans (h.volume m t)
  have hr := transfer_bound (hg t) hy he (Q.price j) (hρ t v).1 (hρ t (fF t)).1 (hK t v) (hK t _) (H' (F j M.L) (g j) le_rfl le_rfl t)
  apply higher_bill hr
  simp only [mul_one]; rw [hj]; exact ht _ _ hn
end level

def LightPath (T : Kin V Z) (f : ℝ→ℝ): Prop:= ∀ N m, m ≤ N→ Light f a m (T.path N m)
lemma plowedBright (h : Paid w a) (hl : ∀ i, 1 ≤ a.clock.loopCap i) (hp : ∀ N,∃ R : PathData G,BranchRow V N R ∧ Light f a N R)
    (hr : ∀ m N,m<N →∀ R, (Light f a (m+1) R ∧ SatPath V N (m+1) R) → ∃ D α ρ, Light f a m D ∧ Bubble V Q Z N m R D α ρ) : ∃ T : Kin V Z, FullPaths T Q ∧ LightPath T f := by
  classical
  have he (N n) (hN : n≤N) :
      ∃ Y : ℕ→PathData G,∃ α : ℕ→ℝ,∃ ρ : ∀ i,GainWire a i,BranchRow V N (Y N) ∧
        (∀ i,n ≤ i → i≤N → Light f a i (Y i) ∧ SatPath V N i (Y i)) ∧ ∀ i, n ≤ i → i < N → Bubble V Q Z N i (Y (i+1)) (Y i) (α i) (ρ i) := by
    induction hN using Nat.decreasingInduction with
    | self =>
      obtain ⟨R,H,hR⟩ := hp N
      refine ⟨fun _=> R,0,fun _ _ _ _=>0,H,fun i hi hu=> ?_,by intros; omega⟩
      rw [le_antisymm hu hi]; exact ⟨hR,H.1⟩
    | of_succ i hi I =>
      obtain ⟨Y,α,ρ,hY,he,H⟩ := I
      obtain ⟨D,w,θ,hB,hD⟩ := hr i N hi _ (he (i+1) le_rfl hi)
      refine ⟨update Y i D,update α i w,update ρ i θ,?_,?_,?_⟩
      · rw [update_of_ne hi.ne']; exact hY
      · intro m hm hv; rcases eq_or_lt_of_le hm with heq|heq
        · subst m; rw [update_self]; exact ⟨hB,hD.lives⟩
        rw [update_of_ne heq.ne']; exact he m (Nat.succ_le_of_lt heq) hv
      intro m hv hx; rcases eq_or_lt_of_le hv with heq|heq
      · subst m; rw [update_self,update_self,update_self,update_of_ne (by omega)]; exact hD
      rw [update_of_ne (by omega : m+1 ≠ i),update_of_ne (by omega : m≠i),update_of_ne (by omega : m ≠ i),update_of_ne (by omega : m≠i)]; exact H m heq hx
  choose Y α ρ H H' HI using fun N=> he N 0 (Nat.zero_le _)
  let V0 : Kin V Z := ⟨α,Y,ρ⟩; refine ⟨V0,⟨?_,fun N m h=> (H' N m (by omega) h).2.row,fun N m p F hm=> (HI N m (by omega) hm|>.steps p F).2.2.2.2⟩,fun N m hm=> (H' N m (by omega) hm).1⟩
  refine ⟨h.stage.symm,h.lengths.symm,fun N m hm=> (H' N m (by omega) hm).2.ties,fun N m hm => (H' N m (by omega) hm).2.bound,
    fun N i=>(H N).2.1 i,fun N i=> (H N).2.2 i,fun N m p hm F=>(HI N m (by omega) hm|>.steps p F).1,
    fun N m p hm F=>?_,fun N m p hm F=> (HI N m (by omega) hm|>.steps p F).2.2.2.1,fun N m hm=> (HI N m (by omega) hm).earns,fun N m p hm F=> ?_⟩
  · exact ⟨(HI N m (by omega) hm|>.steps p F).2.1,(HI N m (by omega) hm|>.steps p F).2.2.1⟩
  exact higher_bill ((HI N m (by omega) hm|>.steps p F).2.2.2.2) (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hl _) (Q.pos _).le) (Real.exp_pos _).le)

section apply
variable {P : MapPrices} {K V : Horizon a} {Z : ChartRatio G} {W : Delays Θ} {y : Bar W} {w : Wait y}
    (h : Paid w a) (hg : ∀ i, GateVolume i ≤ W.shells i) {s₀ A C : ℕ→ℝ}
    (hx : (fun i => (s.profile i).width) ≤ s₀) (hC : C ≤ fun i => (s.profile i).paths)
    (hA : (fun i => (s.profile i).clip.direct)≤A) (hp : Craft.Rack a P K) (hk : Bid.Retained V K)
include hx hC hA h hp hk
lemma bard (B : BasesFine G P A s₀ C) (hu : ∀ m, 1 ≤ T0 a m ∧ T0 a m ≤ a.clock.loopCap m) (N : ℕ) : ∃ R : PathData G,BranchRow V N R ∧ Light f a N R := by
  let i:=a.clock.J N
  have H := hull_fact hp hk (m:=N) (le_refl N)
  have hh : a.params N=s.profile i := by unfold Levels.params Calendar.params; rw [h.stage]
  obtain ⟨R,h1,h2,h3,h4,h5⟩ := B i (a.S.side N) (bound_climb G a N) (a.params N).clip (hh ▸ hA i) (V.H N N) H.2.1 H.2.2.1 H.2.2.2 (fun n=> by rw [hk.1]; exact hp.top ..)
  have he : Light f a N R:= h4 _ _ _ (a.params _).width_pos (hh ▸ hx i) (hh ▸ hC i) (le_trans zero_le_one (hu N).1)
  exact ⟨R,⟨⟨h1,h2,lightUp he (hu N).2⟩,h5,h3⟩,he⟩
end apply

include g
lemma under_light (G : Gauge) (hS : G.Simple) (B : MapPrices) (K : KernelChoices) (B₀ : ℕ→ℝ) (he : ∀ i, 0 ≤ B₀ i) (h : Fluent G) :
    ∃ σ A : ℕ→ℝ,(∀ i,0<σ i) ∧ (∀ i,0≤A i) ∧ ∀ (τ A' : ℕ→ℝ),τ ≤ σ → (∀ i,0<τ i) → A ≤ A' →
    ∃ (d γ : ℕ→ℝ) (u : ℕ→ℕ),(∀ i, 0≤d i) ∧ (∀ i,0<γ i) ∧ ∀ (s : Sheet G), s.kernel=K → Buys s τ A' d u B₀ →
      ∀ (L : Rolls s),∃ (V : ℕ →ℕ) (η : ℕ→ℝ), BudgetGap s L B η ∧ ∀ (Θ : Protection L),
        ∃ Δ : ℕ→ℝ, ∀ (D : Delays Θ) (T : Bar D) (M : Wait T), Δ≤D.betaEntry → V ≤ D.shells → ∀ (Q : PostCost L),Q.η=η → 1≤Q.Γ → Q.c ≤ γ →
        ∀ a : Levels G,Paid M a → ∀ X W : Horizon a, Craft.Rack a B X → Bid.Retained W X →
          ∀ Y : ChartRatio G,LocalRatio Y → ∃ U : Kin W Y,FullPaths U Q ∧ LightPath U f := by
  obtain ⟨σ,A,hσ,hA,H,P⟩ := claiming G hS K B B₀ he
  refine ⟨σ,A,hσ,hA,fun τ A' ht hv hw => ?_⟩
  obtain ⟨d,y,u,F,W,h1,Lh⟩ := P τ A' hv (fun i => (hA _).trans (hw _)) h
  refine ⟨d,fun i=> y i/2,u,fun i=>(h1 i).1,fun i=> half_pos (h1 i).2,fun s hs hB L => ?_⟩
  obtain ⟨η,H'⟩ := scene_gate L B
  choose V hT using fun i => waits_up (F i (L.L i)) (y i) 1 (h1 i).2 zero_lt_one
  refine ⟨fun i=> max (GateVolume i) (V i),η,H',fun Θ=> ?_⟩
  obtain ⟨Δ,hΔ⟩ := summerClocks f g G hS s L Θ (fun i=> W i (L.L i))
  refine ⟨Δ,fun w β b he hl Q hη hg hc a hd X Y hx hy Z HZ => ?_⟩
  have hw₀ := hΔ w β b he a hd
  have hpW i : (s.profile i).width ≤ σ i := (hB.fields i).1.trans_le (ht i)
  have hk i : A i ≤ (s.profile i).paths := (hw i).trans_eq (hB.fields i).2.symm
  have hg' i (n : Side) (hL': w.shells i ≤ n.val) : F i (L.L i) * Real.exp (-(y i)*n.val) ≤ Q.Γ i*Real.exp (-(Q.c i)*n.val) := by
    have hh : Q.c i ≤ y i/2 := hc i
    have hξ : 1≤Q.Γ i := hg i
    refine (hT i n ((le_max_right ..).trans ((hl i).trans hL'))).trans (mul_le_mul hξ (Real.exp_monotone (by gcongr)) (Real.exp_pos _).le (zero_le_one.trans hξ))
  refine plowedBright f hd (fun i=> (hw₀ i).2.2.1.trans (hw₀ i).2.2.2) (fun N=> bard f hd hpW hk hB.axis hx hy H (fun i=>(hw₀ i).2.2) N) fun m N hN R hR => ?_
  refine sunny f hd (hη.symm ▸ H') (fun i=> le_trans (le_max_left ..) (hl i)) hg' hB.axis hpW hk hB.gradient hB.days HZ hx hy ?_ hw₀ hR.1 hR.2.ties hN
  rw [hs]; rw [funext fun i=> (hB.fields i).1,funext fun i=> (hB.fields i).2]; exact Lh

end light

end YM.Stationary
