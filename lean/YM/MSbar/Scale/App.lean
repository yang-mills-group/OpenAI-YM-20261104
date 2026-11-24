import YM.MSbar.Scale.Ray
/-! Apply proof-local ray transforms labeled by multiset of all tags. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Scale
open Dim Symbol Domain Diagram Super Loops Flight Function Set Filter Counter
open scoped Topology BigOperators Classical ContDiff
variable {C E:Type}{W: Edition C}{m j:ℕ}{U:Set ℂ}{d:Bit} {f:Vertex C}{w:Words C m}{F:Functionals C}
-- patch application propagate locally smoothness
abbrev Job (C:Type) := Multiset C → Vec → ℂ
def apply_at (A:Job C)(f:Vertex C): Vertex C := fun i x=> A (skin x) (ray f x)
lemma great_chart {f:Vec→ℂ}(h:∀ {p q}, Great p → Great q → f (p+q)=f p+f q)(hc:∀ (a:ℂ){p},Great p→ f (a•p)=a*f p): Chart ⊤ f Great:=by
   have hh (x y:Vec)(h:x=ᶠ[⊤]y):x=y:= funext (by simpa [EventuallyEq] using h)
   refine ⟨fun {_} _ he=>?_, fun {_ _} _ _ he=> congr_arg f (hh _ _ he), fun {_ _ _} h1 h2 _ he=>Eq.trans (congr_arg f (hh _ _ he)) (h h1 h2), fun {_ _} a _ hp he=> Eq.trans (congr_arg f (hh _ _ he)) (hc a hp)⟩
   rw [hh _ _ he]; simpa using hc 0 (p:=0) (HasTemperateGrowth.const 0)
lemma reform {A:Job C} (h:∀ c,Chart ⊤ (A c) Great) (hf:Live W d f): Cell W d (apply_at A f):= Cell.reform (F:=fun x m t=> ray f t x) h (by simp only [eventually_top]; intro r; exact along (live_cell hf) _) (fun i x=> great_ray hf x)

abbrev sector {U:Set ℂ} (A:Multiset C → ℂ→ Vec → ℂ) := ∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] (c),∀(f:ℂ × (E × ℝ)→ℂ),AH U f→AH U (fun p:ℂ × E=> A c p.1 fun x=> f (p.1,p.2,x))
variable {A: Multiset C→ℂ→ Vec → ℂ}

lemma lined (h: ∀ t z, z ∈ U → Chart ⊤ (A t z) Great) -- implicit? instead explicit
   (ha:sector (U:=U) A)(he:IsOpen U)(hD: U≠univ)(hf:Bright U W d F):Bright U W d (fun z=>apply_at (fun q=>A q z) (F z)):=by
   refine using_cell (fun z hz=>reform (fun c=>h c z hz) (hf.freeze hz)) ?_; intro E i1 i2 i3 m x hx
   refine ⟨?_,fun H=> (hD H).elim⟩
   exact (ha _ (skin (x 0)) _ (bright_ray hf he hx).cost).congr he (fun z hz u=> by rw [Scale.apply_at,Plot.skin_eq hx.1 u 0])
-- convenient pull live from any Profit
lemma devote [h:Profit U] (hf:Bright U W d (liftV f)): Live W d f:=hf.freeze h.around
abbrev disk := Metric.ball (0:ℂ) 1
instance : Profit disk := ⟨fun h=> by have hm : (1:ℂ)∈disk:= h ▸ mem_univ _; simp [disk] at hm,Metric.mem_ball_self (by norm_num),Metric.isOpen_ball⟩ -- fix
lemma live {A:Job C}(hA: ∀ t,Chart ⊤ (A t) Great)(hS:sector (U:=disk) (fun (c:Multiset C) _ => A c))(hf:Live W d f): Live W d (apply_at A f):= devote (lined (fun t _ _=> hA t) hS Profit.pub Profit.proper (F:=liftV f) (cold hf)) -- need expose disk abbreviation public for later
end YM.MSbar.Scale
