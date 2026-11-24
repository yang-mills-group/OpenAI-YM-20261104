import YM.FormalBulk08.Sable.Merriment

/-! Moving budgets down the linear charges with Tap identity. Full row prescription. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Sable
open Reef Flat Lattice Laurent Bloch Exterior Filter Function Next.Free RG Precision Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Grail Work.F03 Work.F05 Work.F08
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G: Gauge} {I J V:Type} {u m n r:ℕ} {η σ A C B:ℝ} {ε θ:ℝ≥0} {L: Side}
lemma fleeing (x:Cover) {T:Tile (Biglot V) m}{o:Biglot V}(h:Knoxville (grain (fame _) θ) η o T A) : Knoxville (grain (fame _) θ) η (tint x o) (carries x T) A:= by
   refine ⟨h.1,le_trans (le_of_eq ?_) h.2⟩; rw [←Equiv.tsum_eq (Equiv.arrowCongr (Equiv.refl _) (Lotus.tint x)) _]; refine tsum_congr fun v=> ?_
   have he : carries x T (Lotus.tint x ∘ v)=T v:= by unfold Kemp.carries jetty; rw [show Lotus.tint (-x) ∘ Lotus.tint x ∘ v=v from funext fun j=>Prod.ext (by simp) (by simp)]
   let R:=grain (fame V) θ; change Gorge.shine η (wide R (Fin.cons (Lotus.tint x o) (Lotus.tint x ∘ v)))*‖carries x T (Lotus.tint x ∘ v)‖ₑ= _; rw [he,← Fin.comp_cons ]; congr 2; simp [wide,fame,capD,grain,R]
lemma fled (x:Cover) {T:Tile (Biglot V) m}(o:V)(h:Knoxville (grain (fame _) θ) η (0,o) T A) : Knoxville (grain (fame _) θ) η (x,o) (carries x T) A:= by convert fleeing x h using 1; exact Prod.ext (by simp) (by simp)
lemma petris {R:Reach V}{T:Tile V r}{o:V}(h:Knoxville (grain R ε) u o T B): Knoxville R 0 o T B:= by
    have he:=penn_shrink h (show (0:ℝ)≤u by positivity); refine ⟨h.1,?_⟩; simpa only [shine_one] using he.2
lemma zesp {x:ℝ}(h:0 ≤ x): x ≤ (L.val:ℝ)*x:= le_mul_of_one_le_left h (by exact_mod_cast L.property)

lemma prismK [Fintype I]{T:Tile (edgeL G) (r+1)}{W:Cross L (Loc G 1) I}{R:Cross L (Loc G 0) I}(f: Fin (r+1)→Cross L (Loc G 1) I)
   (o:edgeL G)(j:I)(ht: Knoxville (fame _) 0 o T A)(hp: Knoxville (grain (fame _) θ) u o (tap T) B)(hs:ε≤1)(h:0<η)(hη:ε≤L.val*θ)(hc:0≤C)(hr:W.strip η C)(hg:R.strip η C)(hf:∀ i, (f i).strip η C)(ha:Agate T)(hx:trench W R)(i:Fin (r+1)): Knoxville (grain (fame _) ε) u (piz L o j) (prism (fun u=>merit (update f i W u)) T) (Real.exp ((u:ℝ)*plum 1 8)* B*(sack u η* (Fintype.card I * C))^(r+1)) := by
    let s:Equiv.Perm (Fin (r+1)):= Equiv.swap 0 i; let U:= prism (fun u=>merit (update (f∘s) 0 W u)) T
    have he (a : Fin (r+1)): update f i W (s a)=update (f ∘ s) 0 W a:= by
       by_cases h:a=0
       · simp [s,h]
       rw [update_of_ne (show s a≠i from fun k=>h (s.injective (k.trans (Equiv.swap_apply_left ..).symm))),update_of_ne h]; rfl
    rw [show prism _ T= _ from (show prism (fun u=>merit (update f i W u)) T=fun v=>U (v ∘ s) from funext fun v=>by rw [rotate_prism _ T v s ha]; unfold U; rw [show (fun u=>merit (update f i W u)) ∘ s= _ from funext fun u=>by rw [comp_apply,he]])]; apply rolling;unfold U;rw [prism_trench hx le_rfl h.le (penn_bail ht le_rfl) (penn_bail (petris hp) le_rfl) hr hg hc (f ∘ s) (fun i=>hf _)]
    exact penn_neg (icy_counts _ _ _ hs hη _ hp h (fun i=>by by_cases h:i=0; simp [h,proxy_pay hg hc]; simp only [update_of_ne h]; exact hf _) hc)
lemma flurries {L:Side}[Fintype I]{T : Tile (edgeL G) r}{R Q:Cross L (Loc G 1) I}{W:Cross L (Loc G 0) I}(c:edgeL G)(j:I)(hs:0<η)(hp:ε≤L.val*θ)(hh:ε≤1)(h:Knoxville (fame _) 0 c T A)(ht:∀ k:ℕ,∀ v:r=k+1, Knoxville (grain (fame _) θ) u c (tap (lengthen v T)) B)
    (hx: Agate T)(he:R.strip η C)(hq:Q.strip η C)(hk:W.strip η C)(hc:0≤C)(hu:trench (minusRows R Q) W): Knoxville (grain (fame _) ε) u (piz L c j) (pearl (merit R) T-pearl (merit Q) T) ((r:ℝ)*(Real.exp ((u:ℝ)*plum 1 8)*B*(sack u η*(Fintype.card I*(C+C)))^r)):= by
   cases r with
   | zero=>
      have heq : pearl (merit R) T=pearl (merit Q) T := by funext v; unfold pearl; simp
      rw [heq, sub_self,Nat.cast_zero,zero_mul]; exact Knox_zeros _
   | succ r=>
     specialize ht r rfl
     let U (P:Finset (Fin (r+1))) (i : Fin (r+1)):= if i∈P then R else Q
     let f (P:Finset (Fin (r+1))):= prism (fun i=>merit (U P i)) T
     rw [show pearl (merit R) T=f Finset.univ by simp only [f,U,Finset.mem_univ,↓reduceIte];rfl,show pearl (merit Q) T=f ∅ by simp only [f,U,Finset.notMem_empty,↓reduceIte];rfl]
     rw [show ((r+1:ℕ):ℝ)= ↑(Finset.univ:Finset (Fin (r+1))).card by simp]; apply stitch
     intro t hx' i _ hi; let Z:=U t
     have hb(k): Row.strip (Z k) η C:= by by_cases hv:k∈t <;>simp [Z,U,hv,he,hq]
     have hx : f (insert i t)=prism (fun u=> merit (update Z i R u)) T:=by
        unfold f; congr 1;funext k; by_cases h:k=i<;> simp [Z,h,U]
     have hz : update Z i Q=Z:= by funext x; by_cases h:x=i <;> simp [h,Z,U,hi]
     let V:= Bank.scroll L (Loc G 1) c
     have hf:= (show Knoxville (fame _) 0 ((Bank.scroll L (Loc G 1)).symm V) T A from by unfold V; rw [Equiv.symm_apply_apply]; exact h)
     have hy:=penn_bail (rinse_bill T L (show 0 ≤ (L.val:ℝ)*0 by simp) le_rfl V hf) le_rfl
     have he': f t= prism (fun u=> merit (update Z i Q u)) T:= by rw [hz]
     rw [hx,he',tower _ _ rfl (update Z i R),tower _ _ rfl (update Z i Q), twin_arcs le_rfl hc _ hy i (strip_mono he hs.le le_rfl) (strip_mono hq hs.le le_rfl) Z (fun i=>strip_mono (hb i) hs.le le_rfl), ←tower _ _ rfl (update Z i (minusRows R Q))]
     exact prismK Z c j h ht hh hs hp (add_nonneg hc hc) (strip_minus he hq) (strip_mono hk le_rfl (le_add_of_nonneg_left hc)) (fun i=> strip_mono (hb i) le_rfl (le_add_of_nonneg_left hc)) ‹Agate T› hu i
variable {j t:ℕ}{K:KernelChoices}
lemma absolution (a : edgeL G) (F:Flight j t)(V:Lodge F.patch)(b:Loc G 1)(hs:0<η)(hp:ε≤F.L.val*θ)(hh:ε≤1){T:Tile (edgeL G) r}(h: Knoxville (fame _) σ a T A)(hf:0<σ)(hx:Agate T)(hv:∀ k:ℕ,∀ v:r=k+1, Knoxville (grain (fame _) θ) u a (tap (lengthen v T)) B) {Z S C:ℝ}
    (he:(Flight.duo K.penalty F).A0.strip η S)(hc:0≤S)(hz:(locating G K F V).strip η C)(hZ:(roots G K F V).strip η Z) :
    let X := (Fintype.card (Bank.Board G F.patch):ℝ)* (1 *(Fintype.card (BoardL G F.patch V)*(1*max 1 C))); let c:=max S (max Z X)
    Knoxville (grain (fame _) ε) u (piz F.L a b) (jetty (coastRight _ _ _) (urn F V G K T) -pearl (merit (chair F G K)) T) (r*(Real.exp ((u:ℝ)* plum 1 8)*B*(sack u η*(Fintype.card (Loc G 1)*(c+c)))^r)) := by
       intro X b; rw [group_track F V K _ _ h (lt_min hs hf) (le_trans (min_le_right ..) (zesp hf.le)) (strip_mono hz (min_le_left ..) le_rfl)]
       let M := chair F G K
       have hy : M.strip η S:= grown_budget G _ hc he
       exact flurries a _ hs hp hh (penn_shrink h hf.le) hv hx (strip_mono (script_pay F V hz hs.le) le_rfl (le_trans (le_max_right Z X) (le_max_right ..))) (strip_mono hy le_rfl (le_max_left ..)) (strip_mono hZ le_rfl ((le_max_left Z X).trans (le_max_right ..))) (hc.trans (le_max_left S _)) (literal F V he hs hc G)
end YM.FormalBulk08.Sable
