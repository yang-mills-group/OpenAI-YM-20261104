import YM.FormalBulk08.Grail.Way

/-! Separate unscaled budgets, instantiated later. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Grail
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {I J V: Type} {r l d u : ℕ} {G : Gauge} {P : Reach V}{x:V}{η θ A B C :ℝ}
lemma tap_shift (T:Tile (edgeL G) (r+1))(x:Cover): tap (carries x T)=carries x (tap T):= by
   funext v; unfold tap Kemp.carries jetty riverP; simp only [Finset.sum_apply,Function.comp_apply,Pi.sub_apply,Lotus.tint_fst,Lotus.tint_snd]; apply Finset.sum_congr rfl; intro i _; unfold Lava.shed; dsimp only; rw [Fin.comp_cons,Fin.comp_cons, show backwards ((v 0).1+-x) i=backwards (v 0).1 i+-x by unfold backwards;abel]; rfl
lemma merge_lane {L:Side}[Fintype I]{T : Tile (edgeL G) r}{R Q:Cross L (Loc G 1) I}{W:Cross L (Loc G 0) I}(c:edgeL G)(j:I)(hs:0≤η)(hp:η≤L.val*θ)(hh:0≤θ)(h:Knoxville (fame _) θ c T A)(ht:∀ k:ℕ,∀ v:r=k+1, Knoxville (fame _) θ c (tap (lengthen v T)) B)
    (hx: Agate T)(he:R.strip η C)(hq:Q.strip η C)(hk:W.strip η C)(hc:0≤C)(hu:trench (minusRows R Q) W): Knoxville (fame _) η (piz L c j) (pearl (merit R) T-pearl (merit Q) T) ((r:ℝ)*(1*(Real.exp (8*η)*B*(Fintype.card I*(C+C))^r))):= by
   cases r with
   | zero=>
      have heq : pearl (merit R) T=pearl (merit Q) T := by funext v; unfold pearl; simp;
      rw [heq, sub_self,Nat.cast_zero,zero_mul]; exact Knox_zeros _
   | succ r=>
     specialize ht r rfl
     let U (P:Finset (Fin (r+1))) (i : Fin (r+1)):= if i∈P then R else Q
     let f (P:Finset (Fin (r+1))):= prism (fun i=>merit (U P i)) T
     change Knoxville _ _ _ (_-_) _
     rw [show pearl (merit R) T=f Finset.univ by simp only [f,U,Finset.mem_univ,↓reduceIte];rfl,show pearl (merit Q) T=f ∅ by simp only [f,U,Finset.notMem_empty,↓reduceIte];rfl]
     rw [show ((r+1:ℕ):ℝ)= ↑(Finset.univ:Finset (Fin (r+1))).card by simp]; apply stitch
     intro t hx' i _ hi; let Z:=U t;
     have hb(k): Row.strip (Z k) η C:= by by_cases hv:k∈t <;>simp [Z,U,hv,he,hq]
     have hx : f (insert i t)=prism (fun u=> merit (update Z i R u)) T:=by
        unfold f; congr 1;funext k; by_cases h:k=i<;> simp [Z,h,U]
     have hz : update Z i Q=Z:= by funext x; by_cases h:x=i <;> simp [h,Z,U,hi]
     let V:= Bank.scroll L (Loc G 1) c
     have hf:= (show Knoxville (fame _) θ ((Bank.scroll L (Loc G 1)).symm V) T A from by unfold V; rw [Equiv.symm_apply_apply]; exact h)
     have hy:=penn_bail (rinse_bill T L hp hs V hf) hs
     have he': f t= prism (fun u=> merit (update Z i Q u)) T:= by rw [hz]
     rw [hx,he',tower _ _ rfl (update Z i R),tower _ _ rfl (update Z i Q), twin_arcs hs hc _ hy i he hq Z hb, ←tower _ _ rfl (update Z i (minusRows R Q))]
     exact tap_arcs Z c j h ht hh hs hp (add_nonneg hc hc) (strip_minus he hq) (strip_mono hk le_rfl (le_add_of_nonneg_left hc)) (fun i=> strip_mono (hb i) le_rfl (le_add_of_nonneg_left hc)) ‹Agate T› hu i
variable {j t:ℕ}{K:KernelChoices}
-- predictors reserves h up chosen before L. C post denominator may pay L if budgets not tight. No factors except strict ancestry here.
def upmost (L:Side)(p:Site L)(S:Cross L (Loc G 1) (Loc G 1))(T:Tile (edgeL G) r): Tile (edgeL G) r := pearl (merit S) (carries (lift p) T)
def lowmost (P:Flight j t)(K:KernelChoices)(V:Lodge P.patch)(p: Site P.L)(T:Tile (edgeL G) r): Tile (edgeL G) r:= jetty (coastRight _ _ _) (urn P V G K (carries (lift p) T))
lemma uranic (a : Loc G 1) (F:Flight j t)(V:Lodge F.patch)(p :Site F.L)(hs:0<η)(hp:η≤F.L.val*θ)(hh:0≤θ){T:Tile (edgeL G) r}(h: Knoxville (fame _) θ (0,a) T A)(hx:Agate T)(hv:Torrid T θ B a) {Z S C:ℝ}
    (he:(Flight.duo K.penalty F).A0.strip η S)(hc:0≤S)(hz:(locating G K F V).strip η C)(hZ:(roots G K F V).strip η Z) :
    let X := (Fintype.card (Bank.Board G F.patch):ℝ)* (1 *(Fintype.card (BoardL G F.patch V)*(1*max 1 C))); let b:=max S (max Z X)
    Knoxville (fame _) η (0,a) (lowmost F K V p T -upmost F.L p (chair F G K) T) (r*(1*(Real.exp (8*η)*B*(Fintype.card (Loc G 1)*(b+b))^r))) := by
       intro X b; let c:edgeL G:=(lift p,a)
       have hA: Knoxville (fame _) θ c (carries (lift p) T) A:= by convert mantle_pay (lift p) h using 1; exact Prod.ext (by simp [c]) rfl
       have hB (k:ℕ)(h:r=k+1): Knoxville (fame _) θ c (tap (lengthen h (carries (lift p) T))) B:= by subst r; change Knoxville _ _ _ (tap (Kemp.carries _ T)) _; rw [tap_shift]; convert mantle_pay (lift p) (current.mp hv) using 1; exact Prod.ext (by simp [c]) rfl
       unfold lowmost;rw [group_track F V K _ _ hA hs hp hz,← show piz F.L c a=(0,a) from chief_h a F _]
       let M := chair F G K
       have hy : M.strip η S:= grown_budget G _ hc he
       exact merge_lane c a hs.le hp hh hA hB (fun v s=>carrying (lift p) s hx v) (strip_mono (script_pay F V hz hs.le) le_rfl (le_trans (le_max_right Z X) (le_max_right ..))) (strip_mono hy le_rfl (le_max_left ..)) (strip_mono hZ le_rfl ((le_max_left Z X).trans (le_max_right ..))) (hc.trans (le_max_left S _)) (literal F V he hs hc G)
end YM.FormalBulk08.Grail
