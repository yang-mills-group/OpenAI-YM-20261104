import YM.FormalBulk08.Grail.Loan

/-! State algebra bills for unchanged tree mean incl gauges. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Grail
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {I J V: Type} {r l d u : ℕ} {G : Gauge} {P : Reach V}{x:V}{η θ A B C :ℝ}

lemma convoy [Fintype I][Fintype J][Fintype V]{p:Tile (Biglot I) r}{S : (n:Side)→Tile (Tor n I) r}{R:Row I J}{K:Row J V}(b:J)(c:V)(a:Biglot I)(h:Kalm η a p S)(hr:R.strip η A)(hp:K.strip η B)(ha:0≤A)(hb:0≤B)(hs:0<η): pearl (lands K) (pearl (lands R) p)=pearl (lands (composeRows R K)) p:= by
   have he:=kalm_stream c hp hb hs (kalm_stream b hr ha hs h); have hh:=kalm_stream c (strip_compose hs.le hr hp) (by positivity) hs h
   funext v; exact tendsto_nhds_unique (he.1 v) ((hh.1 v).congr' (.of_forall fun n=>by dsimp only; rw [acts_compose hs.le hr hp]; exact (congr_fun (Glide.serial _ _ _) _).symm))
variable {j t:ℕ}
lemma group_track (F:Flight j t)(V : Lodge F.patch)(K: KernelChoices)(T:Tile (edgeL G) r)(o:edgeL G)(ht: Knoxville (fame _) θ o T A)(hs:0<η)(h: η ≤ F.L.val* θ)(hv: (locating G K F V).strip η C):
     jetty (coastRight _ _ _) (urn F V G K T)=pearl (merit (script F V G K)) T:= by
   let B:= Bank.scroll F.patch.L (Loc G 1); have hp : Knoxville (fame _) θ (B.symm (B o)) T A:= by rw [B.symm_apply_apply];exact ht
   have he:= sieve_kalm _ (rinse_bill T F.patch.L h hs.le _ hp) hs.le
   have hh:= pane_pay V η (G:=G);have hz:=wing_strip (I:=Bank.Rim G F.patch) (J:=Loc G 1) η;have hb:=zealandPay K F V hv
   have hu:=le_max_left 1 C
   rw [urn, convoy (Sum.inr o.2) (Sum.inr o.2) _ (kalm_stream (Sum.inr o.2) hz zero_le_one hs he) hh hb zero_le_one (zero_le_one.trans hu) hs, convoy (Sum.inr o.2) (Sum.inr o.2) _ he hz (strip_compose hs.le hh hb) zero_le_one (by positivity) hs]; change jetty _ (pearl _ _) = prism (fun _:Fin r=>merit (script F V _ _)) T; exact (tower _ _ rfl (fun _=> script F V G K)).symm

lemma penn_prism {L : Side} [Fintype I][Fintype J](f:Fin r→ Cross L I J)(x:Biglot I)(j:J)(he:∀ i,(f i).strip η C)(p:Tile (Biglot I) r)(hc:0≤C)(hp: Knoxville (fame _) θ x p A)(hη: η≤L.val*θ)(hs:0≤η): Knoxville (fame _) η (piz L x j) (prism (fun i=>merit (f i)) p) (1*((Real.exp (8*η)*A)*(Fintype.card J*C)^r)):= by
    let x':= Bank.scroll L I x; let g:=Bank.scroll L I
    have hh := (show Knoxville (fame _) θ (g.symm x') p A from by unfold x'; rw [g.symm_apply_apply];exact hp)
    have he':=Kemp.rinse_bill p L hη hs x' hh; rw [tower _ _ rfl f]
    exact (quake (x:=x') (y:=(x'.1,j)) (bridge _ _ η hs) (fun i=> lands (f i)) (by simp [bridge,linkshine,Gorge.shine]) he' (fun i=>grad_line _ (he _) hc) (by positivity)).bill
lemma rolling (Z:Tile V r)(h:Knoxville P η x Z A)(s: Equiv.Perm (Fin r)): Knoxville P η x (fun j=> Z (j ∘ s)) A:= by
    refine ⟨h.1,le_trans (le_of_eq ?_) h.2⟩; rw [← Equiv.tsum_eq (Equiv.arrowCongr s.symm (Equiv.refl V)) (fun j:chain V r=> Gorge.shine _ _*‖Z j‖ₑ)]; -- may fail
    refine tsum_congr fun j=>?_ ; have he : (Fin.cons x (j ∘ s) : chain V (r+1))= (Fin.cons x j : chain V (r+1)) ∘ Equiv.Perm.decomposeFin.symm (0,s) := by ext1 i; cases i using Fin.cases <;> simp [Equiv.Perm.decomposeFin_symm_apply_succ]
    change _= Gorge.shine η (wide P (Fin.cons x (j ∘ s):chain V (r+1)))*‖Z (j ∘ s)‖ₑ;rw [he,wide_turn]
lemma tap_arcs {L:Side}[Fintype I]{T:Tile (edgeL G) (r+1)}{W:Cross L (Loc G 1) I}{R:Cross L (Loc G 0) I}(f: Fin (r+1)→Cross L (Loc G 1) I)
   (o:edgeL G)(j:I)(ht: Knoxville (fame _) θ o T A)(hp: Knoxville (fame _) θ o (tap T) B)(hs:0≤θ)(h:0≤η)(hη:η≤L.val*θ)(hc:0≤C)(hr:W.strip η C)(hg:R.strip η C)(hf:∀ i, (f i).strip η C)(ha:Agate T)(hx:trench W R)(i:Fin (r+1)): Knoxville (fame _) η (piz L o j) (prism (fun u=>merit (update f i W u)) T) (1*((Real.exp (8*η)*B)*(Fintype.card I*C)^(r+1))) := by
    let s:Equiv.Perm (Fin (r+1)):= Equiv.swap 0 i; let U:= prism (fun u=>merit (update (f∘s) 0 W u)) T
    have he (a : Fin (r+1)): update f i W (s a)=update (f ∘ s) 0 W a:= by
       by_cases h:a=0
       · simp [s,h]
       rw [update_of_ne (show s a≠i from fun k=>h (s.injective (k.trans (Equiv.swap_apply_left ..).symm))),update_of_ne h]; rfl
    rw [show prism _ T= _ from (show prism (fun u=>merit (update f i W u)) T=fun v=>U (v ∘ s) from funext fun v=>by rw [rotate_prism _ T v s ha]; unfold U; rw [show (fun u=>merit (update f i W u)) ∘ s= _ from funext fun u=>by rw [comp_apply,he]])]; apply rolling;unfold U;rw [prism_trench hx hs h (penn_bail ht hs) (penn_bail hp hs) hr hg hc (f ∘ s) (fun i=>hf _)]
    exact penn_neg (penn_prism _ _ j (fun i=>by by_cases h:i=0; simp [h, proxy_pay hg hc]; simp only [update_of_ne h]; exact hf _) _ hc hp hη h)
lemma stitch [DecidableEq I] (S: Finset I) (f:Finset I →Tile V r)(C:ℝ)(h:∀ t: Finset I,t⊆S→∀ i∈S, i∉t→ Knoxville P η x (f (insert i t)-f t) C): Knoxville P η x (f S-f ∅) (S.card * C) := by
   induction S using Finset.induction with
   | empty=> simp only [Finset.card_empty,Nat.cast_zero,zero_mul,sub_self];exact Knox_zeros _
   | @insert i S he ih=> have ht:= (h S (Finset.subset_insert ..) i (Finset.mem_insert_self ..) he).add (ih (fun t s j hb=>h t (s.trans (Finset.subset_insert ..)) j (Finset.mem_insert_of_mem hb))); rw [sub_add_sub_cancel] at ht; rw [Finset.card_insert_of_notMem he,Nat.cast_add_one,add_mul,one_mul,add_comm];exact ht
end YM.FormalBulk08.Grail
