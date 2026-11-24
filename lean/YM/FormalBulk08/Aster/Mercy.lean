import YM.FormalBulk08.Aster.Bee

/-! Loading steps on varying budgets. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Aster
open Lattice Laurent Bloch RG Precision Wilson Orb Reef City Filter Function Series Wick Jets Stationary Lotus Shore Lava Gorge Mesa Cork Wine Flat Glide Bank Work.F08 Next.Free
open scoped Topology ENNReal BigOperators Classical
variable {G:Gauge} {K:KernelChoices} {X I:Type} {E e r:ℕ} {j t:X→ℕ}(F:∀ x: X, Flight (j x) (t x)) (U:∀ x:X,Lodge (F x).patch) (ρ: ChartRatio G) (H:∀ x:X, (F x).patch.Branches K G)

abbrev graded (D:∀ i:X,Train (j i)) (i:X):= (Flat.Gate.mk (F i)).ride (D i)
structure Freight (K:KernelChoices) (τ:Time X) (σ η:X→ℝ)(E:ℕ) :Prop where
    coverage : ∀ i, η i≤(F i).L.val * σ i
    input : ∀ i, 0<σ i
    output : ∀ i, 0<η i
    blow : Soft τ (fun i=>Real.exp (8 * η i))
    rim : Soft τ (fun i=>(Fintype.card (Rim G (F i).patch):ℝ))
    board : Soft τ (fun i=>(Fintype.card (Board G (F i).patch):ℝ))
    slots : Soft τ (fun i=>(Fintype.card (BoardL G (F i).patch (U i)):ℝ))
    ink : ∀ i,1≤ i→ i≤ E → ∀ r, 1≤r → r≤ i +2 → Cost τ (fun _=> fame _) η (fun k=> TO G (F k).patch K i r)
    soil : ∀ i,1≤ i→ i≤ E → ∀ r,1≤r → r≤ i +2→ Cost τ (fun _=> fame _) η (fun k=> WO (F k).patch (U k) ρ i r)
-- lexer '≤ i'
variable {τ:Time X}{σ η δ:X→ℝ}
structure Honest (K:KernelChoices) (G:Gauge) (L:∀ i:X,Train (j i)) (τ:Time X)(η:X→ℝ)(H:∀ x, (F x).patch.Branches K G) :Prop where
    swirl : ease τ η (fun i=> locating G K (graded F L i) (U i))
    rays : ease τ η (fun i=> Flat.gamma G K (graded F L i) (U i) (H i))
-- no qualified χ except Loc
structure Canvas (τ:Time X)(L M:∀ i:X,Train (j i))(η δ:X→ℝ) :Prop where
    swirl : Maori τ η δ (fun i=>locating G K (graded F L i) (U i)) (fun i=> locating G K (graded F M i) (U i))
    rays : Maori τ η δ (fun i=>Flat.gamma G K (graded F L i) (U i) (H i)) (fun i=>Flat.gamma G K (graded F M i) (U i) (H i))
variable {F U H}{D L:∀ i:X,Train (j i)}
lemma Honest.mock (h:Honest F U K G L τ η H): Canvas F U H τ L L η δ := ⟨maori_constant h.swirl, maori_constant h.rays⟩
lemma Canvas.left (h:Canvas F U H τ D L η δ): Honest F U K G D τ η H:= ⟨h.swirl.left,h.rays.left⟩
lemma Canvas.right (h:Canvas F U H τ D L η δ): Honest F U K G L τ η H:= ⟨h.swirl.right,h.rays.right⟩
lemma Honest.zeal (h:Honest F U K G L τ η H) : ease τ η (fun i=> zealand K (graded F L i) (U i) G):= by
    obtain ⟨C,c,b,P⟩:= h.swirl; exact ⟨_,(soft_coin τ 1).plus c,fun i=>add_nonneg zero_le_one (b i), fun i=> strip_mono (zealandPay K (graded F L i) (U i) (P i)) le_rfl (max_le (le_add_of_nonneg_right (b i)) (le_add_of_nonneg_left zero_le_one))⟩
lemma gaps {J I:Type}{P Q:Row I J}(A:Row I I)(C:Row J I)(B:Row J J) : minusRows (dye A P C B) (dye A Q C B)=dye 0 (minusRows P Q) 0 0:= by
    funext i j x; cases i <;> cases j <;> simp [dye,minusRows]
lemma gap_two {J I:Type}{A B:Row I I}(P:Row I J)(C:Row J I)(Q:Row J J): minusRows (dye A P C Q) (dye B P C Q)=dye (minusRows A B) 0 (0:Row J I) 0:= by
    funext i j x; cases i <;> cases j <;> simp [dye,minusRows]
lemma Canvas.zeal (h:Canvas F U H τ D L η δ) (he:∀ x,0≤δ x): Maori τ η δ (fun i=> zealand K (graded F D i) (U i) G) (fun i=>zealand K (graded F L i) (U i) G):= by
    obtain ⟨C,c,u,P⟩:= h.swirl.lamp; refine ⟨h.left.zeal,h.right.zeal,C,c,u,fun i=>?_⟩
    have hv :0≤ C i*δ i:= mul_nonneg (u i) (he i)
    have hx: minusRows (zealand K (graded F D i) (U i) G) (zealand K (graded F L i) (U i) G)=dye (0 : Row (Minor G (F i).patch (U i)) (Minor G (F i).patch (U i))) (minusRows (locating G K (graded F D i) (U i)) (locating G K (graded F L i) (U i))) (0 : Row (Loc G 1) (Minor G (F i).patch (U i))) 0:= by
       exact gaps (P:=locating G K (graded F D i) (U i)) (Q:=locating G K (graded F L i) (U i)) (unitRow _) 0 (unitRow _)
    rw [hx]; exact fileStrip (stillborn hv) (P i) (stillborn hv) (stillborn hv)
-- open `Silver` ambiguity
variable {ρ} (w:Freight F U ρ K τ σ η E)
include w
lemma Honest.light (h:Honest F U K G L τ η H): Aster.Silver τ (fun i=> fame (BoardL G (F i).patch (U i))) η (fun i=> lands (rayshot (graded F L i) (U i) (H i))) := by
    obtain ⟨B,b,e,P⟩:=h.rays; have hh i := ray_cover (graded F L i) (U i) (H i) (w.output i).le (e i) (P i); exact ⟨fun i=>(hh i).2,_, w.slots.times b, fun i=>(hh i).1⟩
omit w in
lemma gratia {V:Type}[Fintype V]{σ C:ℝ}{S:Row V V}(h:S.strip σ C)(he:0≤C): Grate (fame V) σ (lands S) (Fintype.card V*C) := by
    have he:=grad_line S h he; refine ⟨he.costs,fun x=>?_⟩; have hv:= he.rows x; simp_rw [linkshine,←show ∀ y:Biglot V,(fame _).d y x=size (y.1-x.1) from fun _=>rfl,Reach.turn _ _ x] at hv;exact hv
omit w in
lemma voltage {V I:Type} [Fintype V][Fintype I]{σ C:ℝ}{R S:Row V V}(I1:Row V I)(I2:Row I V)(I3:Row I I)(h:(minusRows R S).strip σ C)(he:0≤C): Grate (fame _) σ (lands (dye R I1 I2 I3)-lands (dye S I1 I2 I3)) ((Fintype.card (V⊕I):ℝ)*C):=by
    have hx: (minusRows (dye R I1 I2 I3) (dye S I1 I2 I3)).strip σ C:= by rw [gap_two]; exact fileStrip h (stillborn he) (stillborn he) (stillborn he)
    exact gratia hx he
lemma Canvas.gilt (h:Canvas F U H τ D L η δ)(he:∀ x,0≤δ x): Gilt τ (fun i=> fame (BoardL G (F i).patch (U i))) η δ (fun i=>lands (rayshot (graded F D i) (U i) (H i))) (fun i=>lands (rayshot (graded F L i) (U i) (H i))) := by
    obtain ⟨C,c,u,P⟩:= h.rays.lamp; refine ⟨Honest.light w h.left,Honest.light w h.right,_, w.slots.times c,fun i=> mul_nonneg (Nat.cast_nonneg _) (u i),fun i=>?_⟩
    have hv:= voltage (0:Row _ (Loc G 1)) 0 0 (P i) (mul_nonneg (u i) (he i))
    rw [mul_assoc]; exact hv
-- common scaffolds
omit w in
lemma Freight.river : ease τ η (fun i=> winging (Rim G (F i).patch) (Loc G 1)):= ⟨_,soft_coin τ 1,fun _=>zero_le_one, fun _=> wing_strip _⟩
omit w in
lemma Freight.rising : ease τ η (fun i=> pane G (F i).patch (U i)):= ⟨_,soft_coin τ 1,fun _=>zero_le_one, fun _=> pane_pay _ _⟩
lemma altitude_pass {T:X→ Pot G}(h:Cost τ (fun _=> fame _) σ (fun i=> T i e r)): Cost τ (fun _=>fame _) η (fun i=> altitude (F i).patch (T i) e r):=by
    obtain ⟨C,c,H⟩:= h; exact ⟨_,w.blow.times c, fun i=> packet_bill _ (w.coverage i) (w.output i).le (H i)⟩
lemma altitude_delta {T M:X→Pot G}(h:Totem τ (fun _=> fame _) σ δ (fun i=> T i e r) (fun i=> M i e r)): Totem τ (fun _=>fame _) η δ (fun i=>altitude (F i).patch (T i) e r) (fun i=> altitude (F i).patch (M i) e r):= by
    obtain ⟨C,c,hp,H⟩:=h.nebula; refine ⟨altitude_pass w h.left,altitude_pass w h.right,_, w.blow.times c,fun i=> mul_nonneg (Real.exp_pos _).le (hp i),fun i=>?_⟩; rw [mul_assoc];exact packet_bill _ (w.coverage i) (w.output i).le (H i)
lemma totem_start (h:Canvas F U H τ D L η δ)(he:∀ x,0≤δ x){T M:X→Pot G} (z:Fin r) (hE:e≤ E)(ha:1≤ e)(hb:r≤e+2)(hh:Totem τ (fun _=> fame _) σ δ (fun i=> T i e r) (fun i=> M i e r)): Totem τ (fun _=> fame _) η δ (fun i=> cola (T i) ρ (graded F D i) (U i) K e r) (fun i=> cola (M i) ρ (graded F L i) (U i) K e r):=by
   have hy: 1≤ r:=by have :=z.isLt;omega
   have hw i:0≤η i:=(w.output i).le
   simp only [cola,if_neg (show e≠0 by omega)]; have h1:=pearl_delta w.rim w.board hw z (maori_constant (Freight.river (F:=F) (η:=η))) he (altitude_delta w hh); have h2:= h1.minus (Totem.constant (w.ink e ha hE r hy hb)); exact pearl_delta w.slots w.slots hw z (h.zeal he) he ((pearl_delta w.board w.slots hw z (maori_constant (Freight.rising (F:=F) (U:=U) (η:=η))) he h2).plus (Totem.constant (w.soil e ha hE r hy hb)))
end YM.FormalBulk08.Aster
