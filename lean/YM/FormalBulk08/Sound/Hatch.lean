import YM.FormalBulk08.Sound.Tetra
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Sound
open Lattice Laurent Bloch RG Precision Wilson Orb Reef City Filter Function Series Wick Jets Stationary Lotus Shore Lava Gorge Mesa Cork Wine Flat Glide Bank Work.F08 Next.Free Chapel Rift Aster Dove Dove.Lab PowerSeries UVExtension UVExtension.Free Matrix Exterior Tree North
open scoped Topology ENNReal BigOperators Classical Matrix
variable {G:Gauge}{I J:Type}{A:Levels G}{K:KernelChoices}{d j t E e r m:ℕ}{W:Lab G K I}{ρ:ChartRatio G}
variable (x:Leaf W.scrolls)(n:Side)(a:hue G)(Y: Pot G)(hp:Use W ρ E)
def unwashed (k:(boxS x n).Choices)(T:Pot G):= out (hospital x n hp) (joy (ρ:=ρ) x n T k)
lemma striker (p:LocalRatio ρ)(hU:Vivid Y)(k:(boxS x n).Choices)(h:Solved (hospital x n hp) (joy (ρ:=ρ) x n Y k)) :
     rancho (unwashed x n hp k Y) (e+1) r=∑ i∈Finset.range (3*(e+1)+1), jetty (coastRight _ _ _) (swim ((limG x).acts n) (rancho (harvestF x n hp Y k)) i (e+1) r) := by
   let H:=hospital x n hp; let P:=joy (ρ:=ρ) x n Y k; let F:=zeta x n
   let T:=rancho (cobalt H P); let U:=rancho (harvestF x n hp Y k)
   have hf: Fiery T:= fun j e he=> wealth x n hp Y hU k p _ _ fun hz=> he ((Bank.quake (cobalt H P) _ _ _).mpr hz)
   change rancho (out H P) _ _=_; rw [show rancho _ _ _= _ from Lava.extraction H P h T rfl hf e r]; apply Finset.sum_congr rfl; intro i hi
   have hz : ∀ a b,T a b=jetty F (U a b):= fun a b=> infer_joust F _ _ _
   rw [← dye_swim F (aqua H.saddle) ((limG x).acts n) (swarm x n hp) U T hz];rfl
include hp in
lemma layers_price : (limG x).strip (W.windowD x) (W.callL x ρ E) ∧ (limY x).strip (W.windowD x) (max 1 (W.callL x ρ E)) := by
   obtain ⟨v,u⟩:= ongoing hp x; have hk:= (W.turn_whose hp x).plus.le
   exact ⟨fileStrip u.value (stillborn hk) (stillborn hk) (stillborn hk),fileStrip (strip_mono Work.F08.strip_unit le_rfl (le_max_left ..)) (strip_mono v.value le_rfl (le_max_right ..)) (stillborn (zero_le_one.trans (le_max_left ..))) (strip_mono Work.F08.strip_unit le_rfl (le_max_left ..))⟩
variable {Y}
lemma arose_curve (k:(n: Side)→(boxS x n).Choices)(hY:Vivid Y)(h:LocalRatio ρ){B:ℝ}(g:Bail (fame _) (W.windowU x) (Y e r) B)(y: Fin r) : Kith (W.windowD x) (camp ρ x Y e r) (fun n=>rancho (harvestF x n hp Y (k n)) e r):= by
   unfold camp harvestF; simp_rw [spire_materials x _ hp _ e r]; by_cases he:e=0
   · simp only [he,↓reduceIte]; exact ⟨fun _=>tendsto_const_nhds,0,.of_forall fun _=>bail_void ..⟩
   simp only [he,↓reduceIte]; let P:= W.pat x; let F:= W.wood x.a x.b; let s:= W.windowD x; let V:= Y
   have hv n : rancho (joust (zeta x n) (joy (ρ:=ρ) x n Y (k n))) e r = _ := Bank.filtered (boxS x n) V ρ (W.toEmpire.bill x.a x.b) hY h F (k n) e r y
   simp_rw [hv]; apply water_pearl (layers_price x hp).2 _ y (hp.zero _) (zero_le_one.trans (le_max_left ..)); unfold ouzo altitude Bank.atlas
   obtain ⟨C,hC⟩:=TO_bail G e r s P K; obtain ⟨U,hU⟩:= WO_bail G e r s F ρ; have hs:= (hp.zero x).le
   have hx:= water_pearl (M:=winging (Rim G P) (Loc G 1)) (wing_strip _) (stable hs (packed_up (hY.civil e r) _) (packet_bill (W.pat x).L (W.turn_whose hp x).ship hs g) y) y (hp.zero x) zero_le_one
   exact (water_pearl (pane_pay F s) (kith_minus hx (stable hs (TO_up G P K e r) hC y)) y (hp.zero x) zero_le_one).add (stable hs (WO_up G F ρ e r) hU y)
lemma cast_curve (k:(n:Side)→(boxS x n).Choices)(hY:Vivid Y)(h:LocalRatio ρ)(g:∀ e r,∃ B:ℝ,Bail (fame _) (W.windowU x) (Y e r) B)(e i r) (y:Fin r) :
     Kith (W.windowD x) (jetty (coastRight _ _ _) (swim (lands (limG x)) (camp ρ x Y) i e r)) (fun n=> jetty (coastRight _ _ (Loc G 1)) (swim ((limG x).acts n) (rancho (harvestF x n hp Y (k n))) i e r)):= by
   let T n:= rancho (harvestF x n hp Y (k n)); have hv a b (hb:0<b) := arose_curve x hp k hY h (g a b).choose_spec (⟨0,hb⟩:Fin b); let P:=limG x; have ht :=(layers_price x hp).1; let s:= W.windowD x; have hs':0<s:=hp.zero _
   have he(n:Side):Grate (lake n _) s (P.acts n) ((Fintype.card (BoardL G (W.pat x) (W.wood x.a x.b)))* W.callL x ρ E):= by
      have he:=trundle n (limG x) ht (W.turn_whose hp x).plus.le hs'.le; refine ⟨he.costs,fun i=>?_⟩; have hu:=he.rows i; simp_rw [rinkshine,skit_sub n _ i.1] at hu; exact hu
   have hx:= kith_swim (landing_row P (Row.rights _ _ ht hs'.le)) _ hs' (Eventually.of_forall he) (fun n=>pastured x n hp) hv i e r (Nat.pos_of_ne_zero (by have :=y.isLt;omega))
   exact boarded hx
end YM.FormalBulk08.Sound
