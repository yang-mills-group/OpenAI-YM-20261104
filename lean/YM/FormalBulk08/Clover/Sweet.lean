import YM.FormalBulk08.Clover.Mell
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Clover
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof Quire
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
variable {G:Gauge}{K:KernelChoices}{E m n l e r j t d D R:ℕ}{X I:Type}{L:Side}{o:Loc G 1}

lemma blade_difference (P:Flight j t)(V:Lodge P.patch)(K:KernelChoices)(T S: Anthem D G)(p:Studio D)(hL:2≤P.L.val) {σ η A B C:ℝ}(he:η≤ P.L.val*σ)(hη:0≤η)(hA:∀ p,Knoxville (fame _) σ (0,o) (T p e r) (A*‖p‖))(hB:∀ p, Knoxville (fame _) σ (0,o) (S p e r) (B*‖p‖))(hz:(zealand K P V G).strip η C)(hC:0≤C) : blade P K V (T-S) d e r hL p=blade P K V T d e r hL p-blade P K V S d e r hL p:= by
   unfold Grail.blade; rw [←smul_sub,←Finset.sum_sub_distrib]; apply congr_arg; apply Finset.sum_congr rfl; intro i _
   let X:= scroll P.L (Loc G 1) (lift i,o); let y:=throughW i D hL p; let R:=winging (Rim G P.patch) (Loc G 1); let U:=pane G P.patch V; let Z:=zealand K P V G
   let A:= carries (lift i) (T y e r); let B:= carries (lift i) (S y e r)
   have H1:=rinse_bill A P.L he hη X (show Knoxville (fame _) σ ((scroll P.L (Loc G 1)).symm X) A _ from by unfold X;rw [Equiv.symm_apply_apply];exact knight _ _ _ (hA y)); have H2:= rinse_bill B P.L he hη X (show Knoxville (fame _) σ ((scroll P.L (Loc G 1)).symm X) B _ from by unfold X; rw [Equiv.symm_apply_apply]; exact knight _ _ _ (hB y)); let f:= (scroll P.L (Loc G 1)).symm; let a:= jetty f A; let b:= jetty f B
   let T0:=pearl (lands R) a; let U0:= pearl (lands R) b; let p':= pearl (lands U) T0; let q:= pearl (lands U) U0; have hx := wing_strip (I:=Rim G P.patch) (J:= Loc G 1) η; have hy:=pane_pay V η (G:=G); have h1:=penn_pearl R X (Sum.inr o) H1 hη hx zero_le_one; have h2:=penn_pearl R X (Sum.inr o) H2 hη hx zero_le_one; have hp:=penn_pearl U (X.1,Sum.inr o) (Sum.inr o) h1 hη hy zero_le_one; have hq:=penn_pearl U (X.1,Sum.inr o) (Sum.inr o) h2 hη hy zero_le_one
   have ht:T0-U0=pearl (lands R) (a-b):= haggle (P:=R) (.inr o) H1 H2 hx zero_le_one hη
   have he':p'-q=pearl (lands U) (T0-U0):= haggle (P:=U) (.inr o) h1 h2 hy zero_le_one hη
   have he:pearl (lands Z) p'-pearl (lands Z) q=pearl (lands Z) (p'-q):=haggle (P:=Z) (.inr o) hp hq hz hC hη
   change jetty (coastRight _ _ _) (pearl (lands Z) (pearl (lands U) (pearl (lands R) (a-b)))) = jetty (coastRight _ _ _) (pearl (lands Z) p'-pearl (lands Z) q);rw [←ht,←he',he]

variable {J U:X→ℕ}{F:∀ x:X,Flight (J x) (U x)}{V:∀ x:X,Lodge (F x).patch}{H:∀ x,(F x).patch.Branches K G}{Z Y:∀ i:X,Train (J i)}{τ:Time X}{σ η δ g μ:X→ℝ}
variable {hL:∀ i,2≤(F i).L.val}{T S:X→ Anthem D G}{W X':X→Pot G}{ρ:ChartRatio G}{a:hue G}

lemma mill_first (w:Wells τ F V H ρ a σ η δ Z Z W W E)(h:∀ i,0≤g i)(hL:∀ i,2≤(F i).L.val)(d u e r:ℕ)(he:e≤E) (hp:∀ j m:ℕ,precede e r j m→ Tender τ o σ g (fun x p=>T x p j m)):
    Mill d r e (graded F Z) V K hL o τ η g T (fun i=> migrates a (graded F Z i) (V i) K (W i) ρ (H i) (hL i) d u (T i)) := by
    constructor
    · simp_rw [dawn_path,add_sub_cancel_left]; exact wells_income w h hL d u _ _ he hp
    intro j k hj; have hx:∀ i m,precede j k i m→ precede e r i m:=fun i m hi=> by unfold precede at *;omega
    exact Matched.left (full_income w h hL d u j k (by unfold precede at *;omega) (fun i m hi =>Matched.constant (hp i m (hx i m hi))) (Matched.constant (hp j k hj)))
lemma brass_crisp {T S:X→Studio D→ Tile (edgeL G) r}(h:Brass τ o η δ g T S): Tender τ o η (fun i=>δ i*g i) (fun i p=> T i p-S i p):= by unfold Tender;simp_rw [mul_assoc]; exact h.3
lemma crisped (w:Wells τ F V H ρ a σ η δ Z Y W X' E)(hδ:∀ i,0≤ g i)(hL:∀ i,2≤(F i).L.val)(d u e r:ℕ)(he:e≤E)(hp:∀ j m:ℕ,precede e r j m→ Brass τ o σ δ g (fun x p=>T x p j m) (fun x p=> S x p j m))
   (ht:∀ i,Qual (T i) o E (σ i)) (hg:∀ i, Qual (S i) o E (σ i)) (h: Tender τ o σ g (fun x p=>S x p e r)) :
    Mill d r e (graded F Z) V K hL o τ η (fun i=>δ i*g i) (fun i=> T i-S i) (fun i=> migrates a (graded F Z i) (V i) K (W i) ρ (H i) (hL i) d u (T i) -migrates a (graded F Y i) (V i) K (X' i) ρ (H i) (hL i) d u (S i)):= by
    constructor
    · let k:=bottle w hδ hL d u e r he hp; have hy:=brass_crisp k; have hw := brass_crisp (blade_pays w.pay w.carts w.dpos hδ hL w.air e r d (T:=S) (S:=S) (Matched.constant h))
      unfold Tender; convert Bear.plus hy hw using 1; ext1 i; ext1 p
      obtain ⟨A,hA,U⟩:= ht i e he r; obtain ⟨B,hB,H1⟩:= hg i e he r; obtain ⟨C,Hc,c,P⟩:= w.carts.left.zeal
      simp only [Pi.sub_apply,dawn_path, blade_difference (graded F Z i) (V i) K _ _ _ _ (w.pay.coverage i) (w.pay.output i).le U H1 (P i) (c i)];abel
    intro j m hj; exact brass_crisp (full_income w hδ hL d u j m (by unfold precede at *;omega) (fun i k hi=>hp i k (by unfold precede at *;omega)) (hp _ _ hj))
end YM.FormalBulk08.Clover
