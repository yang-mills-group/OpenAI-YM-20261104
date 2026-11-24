import YM.FormalBulk08.Clover.Pay
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Clover
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof Quire
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
variable {G:Gauge}{K:KernelChoices}{E m n l e r j t d D R:ℕ}{X I:Type}
variable {J U:X→ℕ} {F:∀ i:X,Flight (J i) (U i)}{V:∀ i:X,Lodge (F i).patch}{τ:Time X}{σ η δ g μ:X→ℝ}
variable {hL:∀ i,2≤(F i).L.val}{o:Loc G 1}{T S:X→ Anthem D G}{Z: Frame G d}

-- boundary where conditional projection price doesn't depend on same-field
-- power. Direct use rank YIELD subtract. Careful slot≥... some letters nil
-- beyond E+R; operator high Π needs costs of smaller k with k>R+E. If slots
-- possible up to d≤R by choice.
structure Mill (d r e:ℕ)(F:∀ i:X,Flight (J i) (U i))(V:∀ i:X,Lodge (F i).patch)(K:KernelChoices) (L:∀ i,2≤(F i).L.val) (o:Loc G 1)(τ:Time X)(η g:X→ℝ)(T S:X→Anthem D G):Prop where
    /-- strict same component on output -/
    mark : Tender τ o η g (fun i p=> S i p e r - blade (F i) K (V i) (T i) d e r (L i) p)
    further : ∀ j k, precede e r j k→ Tender τ o η g (fun i p=> S i p j k)

lemma centerpiece (i:Letter Z)(w:Payroll K Z o F V E R D τ σ η μ)(h: Mill d r e F V K hL o τ η g T S)(hx:∀ j k:ℕ,precede e r j k → Tender τ o σ g (fun i p=> T i p j k))(hE:e≤E)(hr:r≤R+E)(hv:∀ i,Clef o (T i) l)(hp:l≤R)(hw:∀ i:X,Qual (T i) o E (σ i))(hP:∀ j, Faint τ g (fun i=> coeff e (echo Z (T i) j)))(hg:∀ x,0≤ g x) (hj:slots Z i=r): Faint τ g (fun x=> pearlJ Z (S x (inside Z i D) e r) (mint Z i)):= by
    let X1 i p:=blade (F i) K (V i) (T i) d e r (hL i) p; let Y i p:= S i p e r-X1 i p
    have hh : Faint τ g (fun x=> pearlJ Z (Y x (inside Z i D)) (mint Z i)):=label_quote w i h.mark hr
    obtain ⟨A,hA,H,ht,Q⟩:= Prefix_role Z hv hP (fun j m hj _=> hx j m (Or.inl hj)) hg
    obtain ⟨C,hC,Hc⟩:= w.bills e hE r hr l hp
    choose! B hB HB using fun x=>hw x e hE r
    have hp x:= (Hc x).plea (T x) (hv x) _ (ht x) (fun i=>Q i x) (B x) (hB x) (HB x) (hL x)
    have hr: Faint τ g (fun x=> pearlJ Z (X1 x (inside Z i D)) (mint Z i)):= by
       refine ⟨_,hC.radius.times hA,fun x=>mul_nonneg (abs_nonneg _) (H _),fun x=>?_⟩;rw [mul_assoc]; exact ((hp x).1 i hj).trans (mul_le_mul_of_nonneg_right (le_abs_self (C x)) (mul_nonneg (H x) (hg x)))
    obtain ⟨B,b,hB,H⟩:=h.mark; refine (hh.plus hr).lower (fun x=> le_of_eq ?_)
    have hz:= chalk Z (Y x (inside Z i D)) (X1 x (inside Z i D)) (H x _) ((hp x).2 _) (w.width x) (w.width x) (mint Z i); exact congr_arg _ ((show pearlJ Z (S x _ e r) _=_ from Eq.trans (congr_arg (fun v=>pearlJ Z v _) (sub_add_cancel ..).symm) hz)) -- elaboration
lemma lower_coin {S:X→ Anthem D G}(i: Letter Z)(w:Payroll K Z o F V E R D τ σ η μ)(hp:d≤R+E) (h:∀ j, j<e →∀ k,Tender τ o η g (fun x p=> S x p j k))(hv: Faint τ g (fun x=> pearlJ Z (S x (inside Z i D) e (slots Z i)) (mint Z i))): Faint τ g (fun x=> coeff e (echo Z (S x) i)) := by
   simp_rw [echoline]; apply faint_sums _; intro r hr; let k:= Pose.slots Z i; by_cases hz : slots Z i-r≤ e; swap
   · simp_rw [if_neg hz];apply faint_zero
   simp_rw [if_pos hz]; by_cases hx:r=k
   · subst r; unfold k; rw [Nat.sub_self,Nat.sub_zero]; exact hv
   have he :r<slots Z i:= by rw [Finset.mem_range] at hr; unfold k at hx;omega
   exact label_quote (T:=fun x p=>S x p (e-(Pose.slots Z i-r)) r) w i (h (e-(Pose.slots Z i-r)) (by omega) _) (he.le.trans ((slotsFits Z i).trans hp))
lemma Fidelity (w:Payroll K Z o F V E R D τ σ η μ)(h: Mill d r e F V K hL o τ η g T S)(hx:∀ j k:ℕ,precede e r j k → Tender τ o σ g (fun i p=> T i p j k))(hE:e≤E)(hr:r≤R+E)(hv:∀ i,Clef o (T i) l)(hp:l≤ R)(hw:∀ i:X,Qual (T i) o E (σ i))(hP:∀ j, Faint τ g (fun i=> coeff e (echo Z (T i) j)))(hg:∀ x,0≤g x)(hR:d≤R+E)(j)(i:Letter Z)(he:j<e ∨ j=e∧ r ≤ slots Z i):
    Faint τ g (fun x=> coeff j (echo Z (S x) i)):= by
   obtain hh|⟨hh,hy⟩:= he
   · exact lower_coin (S:=S) i w hR (fun k hk m=> h.further k m (Or.inl (lt_trans hk hh))) (label_quote (T:=fun x p=>S x p j (Pose.slots Z i)) w i (h.further j (Pose.slots Z i) (Or.inl hh)) ((slotsFits ..).trans hR))
   rw [hh]; apply lower_coin (S:=S) i w hR (fun k hk m=>h.further k m (Or.inl hk)); rcases lt_or_eq_of_le hy with hy|hy
   · exact label_quote (T:=fun x p=>S x p e (Pose.slots Z i)) w i (h.further e (Pose.slots Z i) (Or.inr ⟨rfl,hy⟩)) ((slotsFits ..).trans hR)
   exact (hy ▸ centerpiece i w h hx hE hr hv hp hw hP hg hy.symm)

lemma ticker (w:Payroll K Z o F V E R D τ σ η μ)(h: Mill d r e F V K hL o τ η g T S)(hx:∀ j k:ℕ,precede e r j k → Tender τ o σ g (fun i p=> T i p j k))(hE:e≤E)(hr:r≤R+E)(hv:∀ i,Clef o (T i) l)(hp:l≤R)(hP:∀ j,Faint τ g (fun i=>coeff e (echo Z (T i) j)))(hg:∀ x,0≤g x):
     ∃ B:X→ℝ,Soft τ B ∧ (∀ i,0≤B i) ∧ ∀ x A',0≤A'→(∀ p : Studio D, Knoxville (fame _) (σ x) (0,o) (T x p e r) (A'*‖p‖)) → ∀ p, Knoxville (fame _) (η x) (0,o) (S x p e r) ((μ x*A'+B x*g x)*‖p‖):= by
   obtain ⟨A,hA,H,ht,Q⟩:= Prefix_role Z hv hP (fun j m hj _=>hx j m (Or.inl hj)) hg
   obtain ⟨C,hC,W⟩:=w.bills e hE r hr l hp; obtain ⟨B,b,hB,Hb⟩:=h.mark
   refine ⟨_, (hC.radius.times hA).plus b,fun i=> add_nonneg (mul_nonneg (abs_nonneg _) (H i)) (hB i), fun x A' ha Hx p=>?_⟩
   have hv:= (Hb x p).add ((W x).plea (T x) (hv x) _ (ht x) (fun i=>Q i x) A' ha Hx (hL x)|>.2 p); rw [sub_add_cancel] at hv; apply hv.mono; apply (add_le_add_right (mul_le_mul_of_nonneg_right (add_le_add_right (mul_le_mul_of_nonneg_right (le_abs_self (C x)) (mul_nonneg (H x) (hg x))) _) (norm_nonneg p)) _).trans_eq; ring
end YM.FormalBulk08.Clover
