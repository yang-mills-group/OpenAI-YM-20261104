import YM.MSbar.Dim.MomentProblem
import YM.MSbar.Dim.Tower

/-! Compose two continued one-loop integrals with **shared dimensional parameter** and both
independent loop variables. Needed for parallel cuts. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Dim
open Function Set Filter Metric Complex MeasureTheory Symbol
open scoped Topology ContDiff BigOperators Classical NNReal
variable {m n : ℕ} {T : ℕ→ Type} {S : Motion T} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
-- shape of double input
abbrev Dual (T : ℕ→Type) := ∀ m,(T m × Hat m) × Hat m → ℂ
variable {F : Dual T} {K H : ℝ} {t : T m} (z : ℂ)
namespace Dual
structure Uses (S:Motion T)(K:ℝ)(F:Dual T) : Prop where
    moves : ((S.prod vectors).prod vectors).Natural F
    ready : ∀ i (x:T i), HasTemperateGrowth (fun p : Hat i × Hat i=> F i ((x,p.1),p.2))
    space : 0 ≤ K
    nulls (i) (x:T i): Vanish K (fun p : Hat i × Hat i=> F i ((x,p.1),p.2))

def inner (S:Motion T) (F:Dual T) (z:ℂ) := request (S.prod vectors) F z
def tower (S:Motion T)(F:Dual T)(z:ℂ):= request S (inner S F z) z
namespace Uses
variable (h : Dual.Uses S K F)
include h
lemma packed (x : T m × Hat m): Packed m K (fun y=>F (m+1) (above (S.prod vectors) x,y)):= Tower.prepares h.moves _ h.space (fun y hy=>
   h.nulls _ (above S x.1) (up m x.2,y) (hy.trans_le (le_max_right ..))) ((h.ready _ (above S x.1)).1.comp (contDiff_const.prodMk contDiff_id))
lemma through : (S.prod vectors).Natural (inner S F z) := Tower.compact_lift h.moves z fun _ x=> ⟨K,h.packed x⟩

lemma ah_one (x : T m) (f : E → Hat m) (hf : f.HasTemperateGrowth) : AH univ (fun p : ℂ×E=> inner S F p.1 _ (x, f p.2)):=by
    let g (a : E × Hat (m+1)):= F _ ((above S x,up m (f a.1)),a.2)
    have hp : g.HasTemperateGrowth:= (h.ready _ (above S x)).comp (tame_pair ((up m).toContinuousLinearMap.hasTemperateGrowth.comp (hf.comp tame_projL)) tame_projR)
    change AH _ (fun p=> plate p.1 (fun y=> g (p.2,y))); exact plate_ah (t:=id) (G:=fun p=>g p.2) (AH.param_tame hp) differentiableOn_id isOpen_univ (fun _ _ y=> h.packed (x,f y))
lemma past (x : T m): Vanish K (fun y=> inner S F z _ (x,y)):= by
    intro q hq; unfold inner request; dsimp only
    rw [show (fun y=> F _ (above (S.prod vectors) (x,q),y))=0 from funext fun y=> by
       exact h.nulls _ (above S x) (up m q,y) (lt_of_lt_of_le (by rwa [(up m).norm_map]) (le_max_left ..)),plate_zero]
lemma packed2 (x:T m): Packed m K (fun y=> inner S F z _ (above S x,y)):= Tower.prepares (h.through z) _ h.space (h.past z _) ((h.ah_one (above S x) id HasTemperateGrowth.id).slice (mem_univ z)).1
lemma natural : S.Natural (tower S F z):= Tower.compact_lift (h.through z) z fun _ x=>⟨K,h.packed2 z x⟩

lemma classical (x:T m) : tower S F (m:ℂ) m x= ∫ p:Hat m,∫ q:Hat m, F m ((x,p),q) := by
    unfold tower; rw [Tower.canonical (h.through _) x (h.packed2 _ _)]; exact integral_congr_ae (Eventually.of_forall fun y=> Tower.canonical h.moves (x,y) (h.packed _))
lemma ah_two (x : T m) : Differentiable ℂ (fun z=> tower S F z m x):=by
    let g(w:ℂ×(ℝ×Hat (m+1))):= inner S F w.1 _ (above S x,w.2.2)
    have hc := plate_ah (G:=g) (K:=K) (U:=univ) (t:=id) (h.ah_one (above S x) _ tame_projR) differentiableOn_id isOpen_univ (fun z _ x=> h.packed2 z _)
    exact fun z=> hc.cr z 0 (mem_univ _)

lemma flip : Dual.Uses S K (fun m p=> F m ((p.1.1,p.2),p.1.2)):=by
    refine ⟨fun ⦃_ _⦄ V x=>h.moves V ((x.1.1,x.2),x.1.2),fun m x=> (h.ready m x).comp (ContinuousLinearEquiv.prodComm ℝ (Hat m) (Hat m)).hasTemperateGrowth,h.space,fun m x q ht=> ?_⟩
    refine h.nulls m x q.swap ?_; simpa [Prod.norm_def,max_comm] using ht
end Uses
end Dual
end YM.MSbar.Dim
