import YM.FormalBulk08.Sierra.Park

/-! Per turn procurement. `Signature` takes ANY starting root &
returns mandatory ancestor residue. Uniform polynomial ζ. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Sierra
open Reef Flat Lattice Laurent Bloch Exterior Filter Function Next.Free RG Precision Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Work.F03 Work.F05 Work.F08 PowerSeries
open Quire Sable Aster Dawn Wine Roof Orb Tundra
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{K:KernelChoices}{E n m u e l r j t:ℕ}{P:Patch}{B C η:ℝ} {X : Type}
-- Exposure erasers
lemma axe_cut (T S:Tile (edgeL G) r)(F:Flight j t)(V:Lodge F.patch)(K:KernelChoices)(o:edgeL G)(hp:Knoxville (fame _) 0 o T B)(hv:Knoxville (fame _) 0 o S C){A:ℝ}(he:(zealand K F V G).strip 0 A)(hA:0≤ A): Det F V K T-Det F V K S=Det F V K (T-S) := by
   let P:= F.L;let f:= scroll P (Loc G 1); let X:= f o; let R:=winging (Rim G F.patch) (Loc G 1); let U:=pane G F.patch V; let Z:=zealand K F V G
   have h1 : Knoxville (fame _) 0 (f.symm X) T B:= by unfold X;rw [Equiv.symm_apply_apply]; exact hp
   have h2 : Knoxville (fame _) 0 (f.symm X) S C:= by unfold X;rw [Equiv.symm_apply_apply]; exact hv
   have hD:0≤(P.val:ℝ)*0:= by simp
   have H1:=rinse_bill T P hD le_rfl X h1;have H2:= rinse_bill S P hD le_rfl X h2
   let x':= f.symm; let a:=jetty x' T;let b:=jetty x' S
   let T0:=pearl (lands R) a;let U0:=pearl (lands R) b;let p':=pearl (lands U) T0;let q:=pearl (lands U) U0
   have hx:=wing_strip (I:=Rim G F.patch) (J:=Loc G 1) 0; have hy:=pane_pay V 0 (G:=G); have h1:=penn_pearl R X (Sum.inr o.2) H1 le_rfl hx zero_le_one; have h2:=penn_pearl R X (Sum.inr o.2) H2 le_rfl hx zero_le_one;have hp:=penn_pearl U (X.1,Sum.inr o.2) (Sum.inr o.2) h1 le_rfl hy zero_le_one;have hq:=penn_pearl U (X.1,Sum.inr o.2) (Sum.inr o.2) h2 le_rfl hy zero_le_one
   have ht:T0-U0=pearl (lands R) (a-b):= haggle (P:=R) (.inr o.2) H1 H2 hx zero_le_one le_rfl
   have he':p'-q=pearl (lands U) (T0-U0):= haggle (P:=U) (.inr o.2) h1 h2 hy zero_le_one le_rfl
   have he:pearl (lands Z) p'-pearl (lands Z) q=pearl (lands Z) (p'-q):=haggle (P:=Z) (.inr o.2) hp hq he hA le_rfl
   change jetty (coastRight _ _ _) (pearl (lands Z) p'-pearl (lands Z) q) = jetty (coastRight _ _ _) (pearl (lands Z) (pearl (lands U) (pearl (lands R) (a-b)))); rw [← ht,←he',he]
-- scalar step. leg words
lemma det0 (T:Tile (edgeL G) 0)(F:Flight j t)(V:Lodge F.patch): Det F V K T=T:= by
    funext v; unfold Det urn jetty pearl;simp; exact congr_arg T (Subsingleton.elim ..)
lemma enterStock (F:Flight j t)(V:Lodge F.patch)(W T:Pot G)(ρ:ChartRatio G)(h:F.patch.Branches K G)(l:ℕ)(a:hue G)(e r:ℕ):
    enterStep F V W a ρ h l T e r=Det F V K (T e r) + (plusB F V W T ρ h l e r+∑ i∈ Finset.range e, Wine.bill (bookH (epoch a F V K W ρ h)) (bookU (epoch a F V K W ρ h)) e i r • braise F V W T ρ h l i r) := by
    let f:= epoch a F V K W ρ h; have he:Wine.bill (bookH f) (bookU f) e e r=1:= by unfold Wine.bill; rw [Nat.sub_self]; exact Fresh.mul ((book_fresh f).pow _) ((book_guard f).pow _)
    unfold enterStep stamp; rw [Finset.sum_range_succ, he,one_smul,braiser F _ _ _ _ _ l e, add_comm]; rw [add_assoc]

variable {τ:Time X}{μ σ η δ g:X→ℝ}{ε θ:X→ℝ≥0}{T S:X→Pot G}{o:X→ edgeL G}
def Wake (τ: Time X)(u:ℕ)(ε:X→ℝ≥0)(o:X→edgeL G) (g:X→ℝ)(T:X→Tile (edgeL G) r):Prop:=Whey u τ (U:=fun _=>Unit) (fun i _=>o i) ε (fun i _=>g i) (fun i _=> T i)
def Wit (τ:Time X)(u:ℕ)(ε:X→ℝ≥0)(o:X→edgeL G)(δ g:X→ℝ)(T S:X→Tile (edgeL G) r):Prop:= Lacy u τ (U:=fun _=>Unit) (fun i _=>o i) ε δ (fun i _=>g i) (fun i _=>T i) (fun i _=>S i)
variable {j t:X→ℕ}{F:∀ x:X, Flight (j x) (t x)}{V:∀ i:X,Lodge (F i).patch}{H:∀ i,(F i).patch.Branches K G}{L N:∀ i:X,Train (j i)}{ρ: ChartRatio G}{a:hue G}{W Y:X→Pot G}
variable (w:Wells τ F V H ρ a σ η δ L N W Y E)(h:Soft τ (fun i=>(η i)⁻¹))(he:∀ i, ε i≤1)(hf: ∀ i, ε i≤(F i).L.val*θ i)
include w h he hf
lemma strict_pair (ht:0<r)(hx:e≤ E)(hp:∀ j k, precede e r j k→ 0<k→ Wit τ u θ o δ g (fun i=> T i j k) (fun i=>S i j k)) : Wit τ u ε (fun i=> chief (F i) (o i) (Exterior.coord 0,a)) δ g
    (fun i=>enterStep (graded F L i) (V i) (W i) a ρ (H i) l (T i) e r-Det (graded F L i) (V i) K (T i e r)) (fun i=>enterStep (graded F N i) (V i) (Y i) a ρ (H i) l (S i) e r-Det (graded F N i) (V i) K (S i e r)):= by
    have ht' i : Fresh (epoch a (graded F L i) (V i) K (W i) ρ (H i)):= (sig_mat a _ (ripeness (F:=F) w.pharmacy w.church w.aV i) K.penalty_pos (w.church i)).1
    have hv i : Fresh (epoch a (graded F N i) (V i) K (Y i) ρ (H i)):= (sig_mat a _ (ripeness (F:=F) w.pharmacy w.church w.bV i) K.penalty_pos (w.church i)).1
    obtain ⟨HA,HB⟩:= w.weight.goods ht' hv
    unfold Wit; simp_rw [enterStock,add_sub_cancel_left]; apply Matched.plus;swap; · apply matched_sums _; intro i hi; rw [Finset.mem_range] at hi; exact Matched.amp (stronger (T:=fun x _=> T x) (S:=fun x _=> S x) w h he hf i r l _ (hi.le.trans hx) (fun j k hk hv=>hp j k (by unfold precede at *;omega) hv) (hp i r (Or.inl hi) ht)) (HA.income HB _ _ r (by omega))
    exact plasters (T:=fun x _=>T x) (S:=fun x _=>S x) w h he hf e r _ _ hx hp
-- on ordered marks
end YM.FormalBulk08.Sierra
