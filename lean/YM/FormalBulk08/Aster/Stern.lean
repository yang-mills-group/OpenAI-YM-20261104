import YM.FormalBulk08.Aster.Mercy

/-! Non-homogeneous assembly into unchanged and strict, before recoupling. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Aster
open Lattice Laurent Bloch RG Precision Wilson Orb Reef City Filter Function Series Wick Jets Stationary Lotus Shore Lava Gorge Mesa Cork Wine Flat Glide Bank Work.F08 Next.Free
open scoped Topology ENNReal BigOperators Classical
variable {G:Gauge} {K:KernelChoices} {X I:Type} {E e r m n:ℕ} (ρ:ChartRatio G)
variable (P:Flight m n)(V:Lodge P.patch)(h:P.patch.Branches K G)

def risePath (G:Gauge) (K:KernelChoices)(T:Tile (edgeL G) r) := jetty (coastRight Cover _ _) (urn P V G K T)
def dirt (K:KernelChoices)(e r:ℕ) := jetty (coastRight Cover _ _) (cola (0:Pot G) ρ P V K e r)
def salt (T:Pot G)(e r:ℕ) := ∑ i∈(Finset.range (3*e+1)).erase 0,jetty (coastRight Cover _ _) (magma P V T ρ h i e r)
def sludge (T: Pot G)(e r:ℕ):= dirt ρ P V K e r + salt ρ P V h T e r
lemma rose_eq {T:Pot G}{σ η A C:ℝ}(z:Fin r)(hx:0<e)(he:0≤η)(ht:η ≤ P.L.val*σ)(H:Bail (fame _) σ (T e r) A) (hC:0≤C)(hs:(zealand K P V G).strip η C): waken P V T ρ h e r =risePath P V G K (T e r)+sludge ρ P V h T e r:=by
    rw [waken,if_neg (by omega),if_neg (by have :=z.isLt;omega),coastRun,←Finset.add_sum_erase _ _ (a:=0) (by simp),sludge,←add_assoc,magma,swim_first];congr 1
    unfold risePath dirt cola; rw [if_neg (by omega), if_neg (by omega)]; symm
    let M:=pane G P.patch V; let L:= lands (zealand K P V G); let U:=atlas P.patch T e r; let W:= TO G P.patch K e r; let X:= WO P.patch V ρ e r
    obtain ⟨A1,hW⟩:= TO_bail G e r η P.patch K; obtain ⟨A2,hX⟩:= WO_bail G e r η V ρ
    have hp:=pane_pay V η (G:=G); have hU:Bail (fame _) η U _:= water_bills (M:=winging (Rim G P.patch) (Loc G 1)) (wing_strip _) (packet_bill P.L ht he H) he zero_le_one
    have hx:Bail (fame _) η (pearl (lands M) U) _ := water_bills hp hU he zero_le_one; have hA : Bail (fame _) η (pearl (lands M) (0-W)+X) _:=(water_bills hp ((bail_void ..).sub hW) he zero_le_one).add hX
    have hf: atlas P.patch (0: Pot G) e r=0:= pearl_zero ..
    unfold ouzo; rw [hf]; change jetty _ (pearl L (pearl (lands M) U))+jetty _ (pearl L (pearl (lands M) (0-W)+X))= jetty _ _
    change jetty (coastRight _ _ _) (pearl L (pearl (lands M) U)+pearl L (pearl (lands M) (0-W)+X))= jetty _ (pearl L (pearl (lands M) (U-W)+X))
    rw [joist (bridge _ _ η he) he hx hA (grad_line _ hs hC) z,←add_assoc,joist (bridge _ _ η he) he hU ((bail_void ..).sub hW) (grad_line _ hp zero_le_one) z]
    rw [←add_sub_assoc, add_zero]

lemma rise_split {σ η A B C:ℝ}{T U:Tile (edgeL G) r} (z:Fin r)(he:0≤η)(ht:η ≤ P.L.val*σ)(H:Bail (fame _) σ T A)(hU:Bail (fame _) σ U B)(hC:0≤C)(hs:(zealand K P V G).strip η C): risePath P V G K T-risePath P V G K U=risePath P V G K (T-U) := by
   let R:=winging (Rim G P.patch) (Loc G 1); have hr:R.strip η 1:= wing_strip _;let M:=pane G P.patch V;have hm:M.strip η 1:= pane_pay _ _
   let g:= (Bank.scroll P.L (Loc G 1)).symm; let L:= lands (zealand K P V G); have hp:= packet_bill _ ht he H; have hx:= packet_bill _ ht he hU; have hp':= water_bills hr hp he zero_le_one; have hx':= water_bills hr hx he zero_le_one
   change jetty _ (pearl L (pearl (lands M) (pearl (lands R) (jetty g T)))-pearl L (pearl (lands M) (pearl (lands R) (jetty g U))))= jetty (coastRight _ _ _) (pearl L (pearl (lands M) (pearl (lands R) (jetty g (T-U)))))
   erw [splits (bridge _ _ _ he) he (water_bills hm hp' he zero_le_one) (water_bills hm hx' he zero_le_one) (grad_line _ hs hC) z, splits (bridge _ _ _ he) he hp' hx' (grad_line M hm zero_le_one) z, splits (bridge _ _ _ he) he hp hx (grad_line _ hr zero_le_one) z];rfl
-- ω funded all strict & individually unchanged
variable {j t:X→ℕ}{F:∀ x: X, Flight (j x) (t x)}{U:∀ x:X,Lodge (F x).patch}{D L:∀ i:X,Train (j i)}(H:∀ x:X,(F x).patch.Branches K G)
variable {τ:Time X}{σ η δ:X→ℝ}
lemma pier_coast {J:Type} {σ A:ℝ}{T:Tile (Biglot (I⊕J)) r}(h:0≤σ)(hp:Bail (fame _) σ T A): Bail (fame _) σ (jetty (coastRight _ _ _) T) A:=
    hp.pier (coastRight Cover I J) (fun _ _ he => Prod.ext (congr_arg (fun x:Cover × (I ⊕ J)=>x.1) he) (Sum.inr_injective (congr_arg (fun x:Cover × (I⊕J)=>x.2) he))) (fun _ _=> le_rfl) h
lemma Cost.shore {I J:X→Type}{W:∀ x:X,Tile (Biglot (I x⊕J x)) r}(h:Cost τ (fun _=> fame _) η W)(hr:∀ x,0≤η x):Cost τ (fun _=> fame _) η (fun x=> jetty (coastRight _ _ _) (W x)) := by obtain ⟨A,u,W⟩:= h; exact ⟨A,u,fun i=>pier_coast (hr i) (W i)⟩
lemma Totem.shore {I J:X→Type}{W M:∀ x:X, Tile (Biglot (I x⊕J x)) r}(h:Totem τ (fun _=> fame _) η δ W M)(hr:∀ x,0≤η x): Totem τ (fun _=> fame _) η δ (fun x=>jetty (coastRight _ _ _) (W x)) (fun x=>jetty (coastRight _ _ _) (M x)) := by
    obtain ⟨A,c,hc,P⟩:=h.nebula; exact ⟨h.left.shore hr,h.right.shore hr,A,c,hc,fun i=>pier_coast (I:=I i) (hr i) (P i)⟩
variable {ρ H}(w:Freight F U ρ K τ σ η E)(c:Canvas F U H τ D L η δ)(he:∀ x,0≤δ x)
include w c he
lemma rise_paid {T M:X→ Pot G}(z:Fin r)(hh:Totem τ (fun _=> fame _) σ δ (fun i=> T i e r) (fun i=> M i e r)): Totem τ (fun _=> fame _) η δ (fun i=> risePath (graded F D i) (U i) G K (T i e r)) (fun i=> risePath (graded F L i) (U i) G K (M i e r)):=by
    have hs i:0≤η i:=(w.output i).le; have h1:= pearl_delta w.rim w.board hs z (maori_constant (Freight.river (F:=F) (η:=η))) he (altitude_delta w hh); have h2 := pearl_delta w.board w.slots hs z (maori_constant (Freight.rising (F:=F) (U:=U) (η:=η))) he h1
    exact Totem.shore (I:=fun i=>Minor G (F i).patch (U i)) (pearl_delta w.slots w.slots hs z (c.zeal he) he h2) hs
lemma pure_soil (z:Fin r)(hE:e≤ E)(ha:1≤ e)(hb:r≤e+2): Totem τ (fun _=> fame _) η δ (fun i=>dirt ρ (graded F D i) (U i) K e r) (fun i=>dirt ρ (graded F L i) (U i) K e r):= by
    exact Totem.shore (I:=fun i=> Minor G (F i).patch (U i)) (totem_start w c he (T:=fun _=>0) (M:=fun _=>0) z hE ha hb (voids ..)) (fun i=> (w.output i).le)
lemma soil_paid (hp:LocalRatio ρ){T M:X→Pot G}(hT:∀ i,Vivid (T i))(hM:∀ i,Vivid (M i))(z: Fin r)(hE:e≤E)(ha:1≤ e)(hb:r≤e+2)(hg:∀ b r',1≤r'→ r'≤b+2 → 1≤b → precede e r b r' → Totem τ (fun _=>fame _) σ δ (fun i=> T i b r') (fun i=> M i b r')):
     Totem τ (fun _=> fame _) η δ (fun i=> sludge ρ (graded F D i) (U i) (H i) (T i) e r) (fun i=> sludge ρ (graded F L i) (U i) (H i) (M i) e r) := by
    refine (pure_soil w c he z hE ha hb).plus (totem_sums _ fun i hi=>?_)
    have hy k:0≤η k:=(w.output k).le; refine Totem.shore (I:=fun i=> Minor G (F i).patch (U i)) ?_ hy
    exact fares_hop hy (fun k=> fairy (T k) ρ (graded F D k) (U k) K (hT k) hp) (Canvas.gilt (F:=F) w c he) (fun k=> fairy (M k) ρ (graded F L k) (U k) K (hM k) hp) (fun b r' q hu hz hx=> totem_start (F:=F) w c he ⟨0,q⟩ (by unfold precede at hx;omega) hz hu (hg b r' q hu hz hx)) i e r (Or.inr ⟨rfl,rfl,Nat.pos_of_ne_zero (Finset.ne_of_mem_erase hi)⟩) (by have :=z.isLt;omega)
end YM.FormalBulk08.Aster
