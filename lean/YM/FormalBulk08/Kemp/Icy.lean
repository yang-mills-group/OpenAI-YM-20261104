import YM.FormalBulk08.Kemp.Loom

noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Kemp
open Reef Lava Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 PowerSeries
open Lotus Shore Mesa Gorge City Cork Rift Stationary
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G : Gauge} (m n : Side) (s:Signed)

lemma widen_Rite (U T:Pap (wire G (m*n))) (h:Rite U T s 0) : Rite (shrink (n:=n) U) (shrink (n:=n) T) s 0 := by
   intro I i a b k A B ha hb hk he hv
   rw [blowing,blowing]; have hz:slope m n 0=0:=by simp [Shore.slope]; -- wraps
   apply h I _ _ (fun i=> k i ∘ (endo m n).residue) (by rw [A];rfl) (by rw [B];rfl) (contDiffAt_pi.mpr fun i=>contDiffAt_pi.mp ha (tray m n i)) (contDiffAt_pi.mpr fun i=>contDiffAt_pi.mp hb (tray m n i)) (fun i=>hk ((endo m n).residue i))
   · obtain ⟨g,h⟩:=he; use g; rw [h];rfl
   filter_upwards [hv] with z hz'; change input _ _ (b z ∘ tray m n) = _; rw [←steep,hz',reborn,tilted_boil,hz,steep]; rfl
lemma subgrade {I : Type} [Fintype I] (p: (m:Side)→Pap (Tor m I))(N:ℕ→ℕ)
    (h : ∀ j,∀ᶠ n in atTop, ∀ l,N j<l→ rancho (p n) j l=0)(j:ℕ): ∀ᶠ m in atTop, ∀ l,N j<l→ rancho (shrink (n:=n) (p (m*n))) j l=0:= by
    filter_upwards [(onward n).eventually (h j)] with m hm k hk; unfold shrink rancho; rw [coeff_map];change marble _ (MvPolynomial.rename _ _)=0; rw [Shore.pebble, show marble _ _=_ from hm k hk]; funext; simp [cores]
lemma verdict {g t: Pap (wire G n)}{V S:(n:Side)→Pap (wire G n)}{P Q:Pot G}{x y} (hv:∀ m,Rite (V m) (S m) s 0)(N M:ℕ→ℕ)
    (h:∀ j,∀ᶠ m in atTop,∀ l,N j<l → rancho (V m) j l=0) (e:∀ j,∀ᶠ m in atTop, ∀ l,M j<l→ rancho (S m) j l=0)
    (H:∀ j r,∃ η : ℝ, 0<η ∧ Kalm η x (P j r) (fun k=>rancho (V k) j r))(E:∀ j r,∃ η:ℝ,0<η ∧ Kalm η y (Q j r) (fun k=>rancho (S k) j r))
    (H':∀ j r,rancho g j r=sieve n (P j r))(E':∀ j r,rancho t j r=sieve n (Q j r)) : Rite g t s 0 := by
    intro I i a b k ha hb hz hs hk hv' Ht; ext1 m; ext1 l; let V' m:=shrink (n:=n) (V (m*n)); let S' m:=shrink (n:=n) (S (m*n))
    have he m:Rite (V' m) (S' m) s 0 := widen_Rite m n _ _ _ (hv _)
    refine tendsto_nhds_unique ((keepsake V' g (motor a) N (subgrade n _ _ h) ?_ m l).congr' (.of_forall fun n=> ?_)) (keepsake S' t (motor b) M (subgrade n _ _ e) ?_ m l)
    · intro j r w; obtain ⟨η,hη,hH⟩:=H j r; exact copy_singleton n V g j hH hη (H' j r) w
    · rw [show roam ℝ (motor a) (V' n)=_ from he n I a b k ha hb hz hs hk hv' Ht]
    intro j r w; obtain ⟨η,hη,hH⟩:=E j r; exact copy_singleton n S t j hH hη (E' j r) w
end YM.FormalBulk08.Kemp
