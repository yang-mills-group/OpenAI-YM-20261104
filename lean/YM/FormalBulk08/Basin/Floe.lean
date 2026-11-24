import YM.FormalBulk08.Basin.Alpha
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Basin
open Reef Flat Lattice Laurent Bloch Exterior Filter Function Next.Free RG Precision Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Work.F03 Work.F05 Work.F08 PowerSeries
open Vale Quire Sable Aster Dawn Wine Roof Orb Tundra Sierra Wick Series
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{X I J V:Type*}{r n m i j t d l E:ℕ}{σ A B C:ℝ}
variable {X: Type} {J:X→Type*}{τ:Time X}{K:KernelChoices}{F F':X→ℕ}{H:∀ i:X,Flight (F i) (F' i)}{P:∀ i:X,Lodge (H i).patch}{k:∀ i,(H i).patch.Branches K G}
variable {η σ δ:X→ℝ}{U V:∀ i:X,Train (F i)}{ρ:ChartRatio G}{W Z:X→ Pot G}{a:hue G}{ε:X→ℝ≥0}
variable {T S:I→∀ i:X,J i→Pot G}{x:I→∀ i:X,J i→edgeL G}{y:∀ i:X,J i→edgeL G}{b:I→∀ i:X,J i→ℝ}{g:∀ i:X,J i→ℝ}
variable (w:Wells τ H P k ρ a σ η δ U V W Z E)(hx: ∀ i, ε i≤1)(hs:Soft τ (fun i=>(η i)⁻¹))(κ:Loc G 1)(L:List I)(μ:I→ℕ)
variable (ht:∀ i∈L,∀ j p,Ritual (T i j p) (μ i))(self:∀ i∈L,∀ j p,Ritual (S i j p) (μ i))(hG:∀ i∈L,∀ e≤E,∀ r, Matched τ (fun _=>fame _) (x i) σ δ (b i) (fun j p=> T i j p e r) (fun j p=> S i j p e r))
    (hV:L.Pairwise (fun i j=> Chasm τ (fun _=>fame _) η (fun z u=> chief (H z) (x i z u) κ) (fun z u=>chief (H z) (x j z u) κ) g))
    (hb:∀ i∈L,Mountain τ (fun _=>fame _) ε (fun z u=>chief (H z) (x i z u) κ) y)
include w hx ht hs self hG hV hb
lemma plow (e r:ℕ)(he:e≤ E)(u:ℕ) : Lacy u τ y ε δ (fun i j=>cartwork L b i j*g i j)
   (fun z p=>fallout (graded H U z) (P z) ρ (W z) (k z) a (fun i=> T i z p) μ L e r) (fun z p=> fallout (graded H V z) (P z) ρ (Z z) (k z) a (fun i=> S i z p) μ L e r) := by
   obtain ⟨A,B⟩:= w.weight.goods (fun i=>(sig_mat a _ (ripeness (F:=H) w.pharmacy w.church w.aV i) K.penalty_pos (w.church i)).1) (fun i=>(sig_mat a _ (ripeness (F:=H) w.pharmacy w.church w.bV i) K.penalty_pos (w.church i)).1)
   have hQ z (p:J z):=glacier (graded H U z) (P z) ρ (W z) (k z) a (fun i=> T i z p) μ L (fun i hi=>ht _ hi z p) (w.aV z) w.pharmacy (w.church z) (y z p)
   have hw z (p:J z):=glacier (graded H V z) (P z) ρ (Z z) (k z) a (fun i=> S i z p) μ L (fun i hi=>self _ hi z p) (w.bV z) w.pharmacy (w.church z) (y z p)
   simp_rw [hQ,hw]; unfold Lacy stamp; apply matched_sums; intro i hi; rw [Finset.mem_range] at hi; refine Matched.amp (matched_sums _ (fun j hj=>?_)) (A.income B _ _ r (by omega)); exact colds (tipCon w hx hs κ L μ ht self hG hV hb i r (by omega) u j)
end YM.FormalBulk08.Basin
