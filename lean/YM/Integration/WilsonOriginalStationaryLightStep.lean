import YM.FullVolume.Canvas.Mails
import YM.QuadraticLocal.PurchaseExtra.Light

set_option autoImplicit false
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Supply
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {s : Sheet G} {L : Rolls s} {Θ : Protection L} {a : Levels G}
theorem expandedLight {G : Gauge} {a : Levels G} {i : ℕ} {R : PathData G}
    (cap : ℝ → ℝ) (large : 1 ≤ cap (a.clock.hatBeta i)) (hy : Light cap a i R) :
    R.Bounds (a.params i).clip (a.params i).width ((a.params i).paths*64) (64*cap (a.clock.hatBeta i)) := by
  have he := le_mul_of_one_le_right (a.params i).paths_pos.le (show 1≤(64:ℝ) by norm_num)
  have hp := le_mul_of_one_le_left (zero_le_one.trans large) (show 1≤(64:ℝ) by norm_num)
  refine { hy with rows := fun x => ⟨(hy.rows x).1,(hy.rows x).2.1,(hy.rows x).2.2.trans he⟩,
                   two := ⟨hy.two.1,hy.two.2.1,hy.two.2.2.trans hp⟩,
                   three := ⟨hy.three.1,hy.three.2.1,hy.three.2.2.trans he⟩,
                   four := ⟨hy.four.1,hy.four.2.1,hy.four.2.2.trans he⟩ }

variable {P : MapPrices} {K V : Horizon a} {Z : ChartRatio G} {W : Delays Θ} {y : Bar W} {w : Wait y} {Q : PostCost L}
section level
variable {Zc A σ d g : ℕ → ℝ} {u : ℕ → ℕ} {F T : ℕ → Side → ℝ} {Zt:ℕ→ℕ→Reel G} {m N : ℕ}
variable (h : Paid w a) (hΘ : BudgetGap s L P Q.η) (hS : ∀ i, GateVolume i ≤ W.shells i) (ht : ∀ i (n : Side),W.shells i ≤ n.val → F i (L.L i)*Real.exp (-(g i)*n.val) ≤ Q.Γ i*Real.exp (-Q.c i*n.val))
variable (hi : (fun i=> (s.profile i).clip.direct) ≤ Zc) (hw : (fun i=> (s.profile i).width) ≤ σ) (hA : A ≤ fun i => (s.profile i).paths)
    (hq : d ≤ fun i => (s.profile i).drift) (hp : u≤ s.floorL) (he : LocalRatio Z)
    (hb : Craft.Rack a P K) (hk : Bid.Retained V K) (hJ : Perform G P s.kernel Zc σ A (fun i=> (s.profile i).width) (fun i=> (s.profile i).paths*64) d g u Zt F T)
include h hΘ hS ht hi hw hA hq hp he hb hk hJ
theorem florentineLight (cap : ℝ → ℝ) (H : ∀ m,let j := a.clock.J (m+1); T j (L.L j) ≤ cap (a.clock.hatBeta m) ∧ cap (a.clock.hatBeta (m+1))/2 ≤ cap (a.clock.hatBeta m) ∧ 1 ≤ cap (a.clock.hatBeta m) ∧ cap (a.clock.hatBeta m) ≤ a.clock.loopCap m) {R : PathData G} (small : Light cap a (m+1) R) (hu' : Attached (V.H N (m+1)) R) (hm : m < N) :
    ∃ D α ρ,Light cap a m D ∧ Bubble V Q Z N m R D α ρ ∧ let i:= a.clock.J (m+1); let j:= a.clock.J m; (Zt i j).Wing (a.S.side m) D (a.params m).paths (a.clock.loopCap m):= by
  have hy := expandedLight cap ((H (m+1)).2.2.1) small
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
  let f := fun t => a.S.side m t; let c := fun t=> a.S.side (m+1) t
  have hv t (F : Forest (a.clock.op m t).ratio) := hΘ.ask j (a.clock.op m t) h.kernel hj rfl (hg t) F z b U.clip T'.clip R U.width (U.paths*64) _ _ _ _ p (Ld t) (hF.2.2.1 _) hy hu' (hF.2.2.2 t) (hT'.2.2.1 _)
  have hK t F := (hv t F).1
  choose ρ hρ using fun i F=> (hv i F).2
  let fF (t : ℕ) : Forest (a.clock.op m t).ratio := Classical.choice (Tree.select _ M.odd_side)
  let ξ : Armada f c M C.kernel := ⟨fun t=> (a.clock.op m t).sizes⟩
  let a' := fun i=> ρ i (fF i)
  have hZ : Fluxed G C.kernel j (P.η j) (P.α j) (pacesE P j) (Zc j) (P.α i) (pacesE P i) (Zc i) (U.paths*64) U.width (A i) (d j) (σ i) (g j) (Zt j i) (u j) (F j) (T j) := by rw [hu,show C.kernel=s.kernel from h.kernel]; exact hJ.moon j i h'
  have hΦ : Scud ξ G U.clip T'.clip R fF a' (P.α j) U.width (pacesE P j) (U.paths*64) (pacesE P j) (P.η j) (64*cap (a.clock.hatBeta (m+1))) (P.α i) (pacesE P i) (P.η i) z b p (Q.η j) :=
      ⟨hg, hF,hT',hu',hy,h2,Ld,fun t=> hK t _,fun i=> (hρ i _).1,fun i=>(hρ i _).2.1, fun i=>(hρ i _).2.2⟩
  obtain ⟨Y,α,hX,hY,hP,hE,hG,H'⟩ := hZ f c M ξ U.clip T'.clip R fF a' z b p (64*cap (a.clock.hatBeta (m+1))) (P.η i) (Q.η j) Z rfl (by rw [hj]; exact (hp j).trans (L.large j).need) (bound_climb G a m) (hu ▸ hi j) (hT ▸ hi i) hΦ (by linarith only [(H (m+1)).2.2.1]) (Q.price _) he
  obtain ⟨hy',hr,_,capBound⟩ := H m
  have hSmall : Light cap a m Y := (hP T'.width T'.paths (cap (a.clock.hatBeta m)) (a.params _).width_pos (hT ▸ hw i) (hT ▸ hA i) (by rw [hj]; exact hy') (by linarith only [hr])).1
  have hZ := hP T'.width T'.paths (a.clock.loopCap m) (a.params _).width_pos (hT ▸ hw i) (hT ▸ hA i) (by rw [hj]; exact hy'.trans capBound) (by linarith only [hr,capBound])
  obtain ⟨hSat,hΩ⟩:=hZ
  refine ⟨Y,α,ρ,hSmall, ⟨hE.trans (show d j ≤ U.drift from hu ▸ hq _), ⟨hX,hY,hSat⟩,fun t v => ⟨hK t v,(hρ t v).1, (hρ t v).2.1,?_,?_⟩⟩,hΩ⟩
  · exact Bid.one_for_all (a.clock.op m t) Work.F05.answer (hg t) (fF t) U.clip T'.clip R Y U.width (U.paths*64) _ _ (Q.price _) hy Z he (ρ t) (fun F=> (hρ t F).1) (hK t) (hG t) v
  have hn : W.shells j ≤ (f t).val := (Nat.le_mul_of_pos_right _ (by positivity)).trans (h.volume m t)
  have hr := transfer_bound (hg t) hy he (Q.price j) (hρ t v).1 (hρ t (fF t)).1 (hK t v) (hK t _) (H' (F j M.L) (g j) le_rfl le_rfl t)
  apply higher_bill hr
  simp only [mul_one]; rw [hj]; exact ht _ _ hn
end level
end YM.Stationary
end
