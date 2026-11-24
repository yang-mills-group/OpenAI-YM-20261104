import YM.FVA2.O.Read.Loft
/-!
# Test-wise version of OPE conversion

Smear the OPE coefficient functions themselves, against a fixed separated inner test.
See `mentions` for conversion.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Canon
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick Metric Real TopologicalSpace
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical Matrix ComplexOrder
open FVA2.Scale MS.Rake MS.Theater Level O.Score LogTime MS.Plane MS.Heat MS.Tone Momentum Rake.Geo
open Equator Facets Dframe O.Enh O.Bind O.Project O.Read
variable { G:Gauge }{ n m d : ℕ }{ A:Album G }{ T U:Cast G }{ u:Scan G n } {t v:ℝ}{K:Set (Points n)}{q:Cn}
variable { f g:Fable G n }{ c:FLog G n }{u w:Scan G n}{B:Scan G n→ Fable G n}{H:ℝ→ Frames G}
abbrev Yield (t: Test n)(c:Fable G n)(b:Q G) : Cn:= Read.smearing t (fun x=> c x b)
lemma honest_S (t:Test n)(h:PaceX f)(b:Q G): draw t ( fun x=> f x b ):= fun i=> ( h b i ).mono t.tsupport_subset
lemma price_rolling (t:ℝ)(h:Markup c)(v: Scan G n): PaceX ( QuoteP v c t ):= by intro b i; exact stableV ( A₁:=fun _=> PowerSeries.C ( Score.fee t ( ( heft b:ℝ )-( totalG v:ℝ) ) )) (fun _=>continuousOn_const) ( fun i=> h.stays t b i ) _
lemma time_κ {f:Points n→Cn}(t:Test n)(h:draw t f)(hp:Rooted q) : ( Read.smearing t f ).subst q= Read.smearing t (fun x=>( f x ).subst q ):= by
    ext i; rw [← Constants.actual_subst _ _ hp ]; unfold Read.smearing; simp_rw [← Constants.actual_subst _ _ hp,coeff_mk,rules,smul_eq_mul]; rw [ Read.smear_sum ]; · simp_rw [ Read.smear_one ]
    exact fun j _=> ( h j ).const_mul _
lemma store_R (t:Test n)(he:PaceX f)(b:Q G): receipt T ( Yield t f ) b= Yield t ( fun x=> receipt T ( f x ) ) b:= by
    unfold Project.receipt Yield; rw [ smearing_sum ]; · apply Finset.sum_congr rfl; intro j _; simp_rw [ mul_comm _ ( T _ j _ ), smearing_mul t ( honest_S t he ( own j ) ) ] -- mul rew all? works
    intro i _; simp_rw [ mul_comm _ ( T _ i _ ) ]; exact Read.region t (honest_S t he ( own i ) ) _
lemma store_c (t:Test n)(h:∀ i,PaceX ( B i ))(he:Rooted q)(b:Q G): credit T q ( fun i=> Yield t ( B i ) ) u b= Yield t ( fun x=> credit T q (fun i=> B i x) u ) b:= by
    unfold credit Yield concert; rw [smearing_sum ]; · apply Finset.sum_congr rfl; intro j _; let F:= fun x=> B ( decode u j ) x b; have hx : draw t F:= honest_S t ( h _ ) b; have ht: draw t ( fun x=>( F x ).subst q ) := continual_k hx he; dsimp only; rw [time_κ t hx he, smearing_mul t ht ] -- inference
    intro i _; exact Read.region t ( F:=fun x=> (B ( decode u i ) x b).subst q ) ( continual_k ( honest_S t ( h _ ) b ) he ) _
def Gift_shape (T:Cast G)(q:Cn)(u:Scan G n)(A: Scan G n→ Fable G n)(b:Fable G n): Prop:=∀ x, Gift T q u ( fun i=> A i x ) ( b x )
lemma mentions (p:Test n)(h: Gift_shape T q u B f)(he:PaceX f)(hv:∀ i,PaceX ( B i ))(hp:Rooted q): Gift T q u ( fun i=> Yield p ( B i ) ) ( Yield p f ) := by unfold Gift; funext b; rw [store_c p hv hp b,store_R p he b]; exact congr_arg (fun f=> Yield p f b) (funext ( fun x=> h x )) -- type
end YM.FVA2.O.Canon
