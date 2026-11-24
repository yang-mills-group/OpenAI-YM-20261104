import YM.MS.Dock.Unify
/-!
# The classical scaling limit of trees of length endpoints
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Dock
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color _root_.YM.MS.Shine Hem Mell Logarithm Pearl Train
open Signal Book Convolve Garment.Wave Garment.Wick
open scoped Topology ContDiff Interval
variable {I A:Type}{G:Gauge}{X Y:Flats G}{F L:Mob G}{u v:Rip G}{f g:Coat G}{b c:Bool}{t v' r:ℤ}{n m h ℓ:ℕ}{i:ℂ}
abbrev limp (U:ℝ→Rip G)(K:Rip G) := ∀ m i j p, Tendsto (fun s=> U s m i j p) atBot (𝓝 (K m i j p))
variable (G)
lemma limitA : limp (A0 G) 0:= by
    intro m i j p; simp only [A0,Landau.choir,Pi.zero_apply,id_eq]; split; swap; exact tendsto_const_nhds
    have hu : Continuous (fun r:ℝ=>City.L0 r i.1 j.1 p):= by rcases i with ⟨⟨_|a,_|_⟩,b⟩ <;> rcases j with ⟨⟨_|a,_|_⟩,b⟩ <;> simp only [City.L0,City.brush] <;> fun_prop
    simp_rw [← City.brushed]; convert! ( Complex.continuous_ofReal.continuousAt.tendsto.comp tendsto_exp_atBot ).mul (hu.continuousAt.tendsto.comp tendsto_exp_atBot) using 1; simp -- hu redundant s binder
lemma limitB : limp (B0 G) (D0 G):= by
    intro m i j p; unfold B0 D0 Landau.choir; split; swap; exact tendsto_const_nhds
    rw [← City.χ0]; exact (City.lap_der 0 i.1 j.1 p).continuousAt.tendsto.comp tendsto_exp_atBot
variable {G}
lemma wind_arbor {f g:ℝ→Mob G}{K:Rip G}{U:ℝ→ Rip G}(he: limp U K)(hp:Wind f atBot F)(ht:Wind g atBot L): Wind (fun x=> arbor (U x) (f x) (g x)) atBot (arbor K F L):= by
    intro m w; let p := Landau.parity (C:=G.ColorIndex) (A:=Arts.L m); let H(x:ℝ)(l r:Legs (Shore G m)) := attaches p (U x m) (f x m) (g x m) l r; let M(l r:Legs (Shore G m)):= attaches p (K m) (F m) (L m) l r
    have hx (T:ℝ→ Shared (Shore G m) ℂ)(S:Shared (Shore G m) ℂ)(h:∀ i j,Tendsto (fun x=>T x i j) atBot (𝓝 (S i j))): Tendsto (fun x=> scatter (field p) w (T x)) atBot (𝓝 (scatter (field p) w S)):= by
        induction w generalizing T S with| nil=> exact h _ _| cons a w ih=> exact ih _ _ (fun i j=> (h _ _).add ((h _ _).const_mul _))
    exact hx H M (fun l r=>by unfold H M attaches; dsimp only; apply tendsto_finsetSum; intro i hi; apply tendsto_finsetSum; intro j hj; apply Tendsto.add <;> exact (he m _ _ _).mul (((hp m _).const_mul _).mul (ht m _))) -- t=z operand? inspect
lemma sipair (hp:Return X f m)(hv:Return Y g n)(he:reverseF u)(a:ℂ)(hx:a-(m:ℂ)-n=-(h:ℂ))(hU:limp (fun t=> pulse a t u) v): Return (TreeN u X Y) (tapeB ( squad v) f g) h:= by
    unfold Return TreeN; rw [explode_zero]; refine (hp.and hv).mono (fun i hi=>?_); let U(t:ℝ):= pulse a t u; let P(t:ℝ):= plow (-(m:ℂ)) t (X 0 i); let L(t:ℝ):= plow (-(n:ℂ)) t (Y 0 i); obtain H:=wind_arbor (F:=f i) (L:=g i) hU hi.1 hi.2; refine Wind.congr H (Eventually.of_forall fun j=>?_); dsimp only; rw [air_tree _ _ _ j he]; simp only [← sub_eq_add_neg,hx]; rfl
lemma zeroA : tapeB (squad (0:Rip G)) f g=0:= by funext i; convert (down_leg (0: Rip G) 0 (f i) (g i)) using 1; simp; rfl; simp
lemma sip_pp (hX:Return X f 4)(hY:Return Y g h): Return ( TreeN (A0 G 0) X Y) 0 h:= by
    have hc : limp (fun t=> pulse 4 t (A0 G 0)) 0:= by simp_rw [pA]; exact limitA G
    rw [← zeroA (f:=f) (g:=g)]; exact sipair hX hY ( reverse_a G 0) 4 (by push_cast; ring) hc
lemma sip_B (hX:Return X f 4)(hY:Return Y g h): Return (TreeN (B0 G 0) X Y) (tapeB (squad (D0 G)) f g) (h+1):= by
    have ht : limp (fun t=>pulse 3 t (B0 G 0)) (D0 G):= by simp_rw [pB]; exact limitB G
    exact sipair hX hY (reverse_b G 0) 3 (by push_cast; ring) ht
lemma sip_Q (hf: Return X f h): Return (QN G X) (tapeL (fun _=>sweepQ (Q G)) f) (h+1) := by
    unfold Return QN; rw [show blast 0 _ X 0=tapeL _ (X 0) from blade 0 X (tapeL (fun _=>sweepQ (Q G))) 0]; apply hf.mono; intro i hi m l; change Tendsto (fun t=> plow _ t (portZ (Q G) ( X 0 i)) m l) _ (𝓝 (portZ (Q G) (f i) m l)); simp_rw [show (-(↑(h+1):ℂ))= -(h:ℂ)-1 from by push_cast; abel,← pole_amp _ (lawQ G)]; exact Wind.center hi _ ((sense_Q ((Q G) m)).reaches l) -- unfolds metav? fail
end YM.MS.Dock
