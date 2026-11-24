import YM.LocalLTE.Frame.Lint
import YM.LocalLTE.Tile.Allot
/-! To reel. Insert on complete auxiliary pre-normalization at true coupling, with
signed scalarized comparison. Here all background settlers at once. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Frame
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat SliceRows
open AbsoluteSums PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard Inset
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {L c f : Side} {j n : ℕ} {a Y d₀ d v q p T c' : ℝ} {χ:Chi} {B:BudgetPoint}
local notation "E" => Positions (Uniform.Primary c G)
local notation "r" => Blaze.royalty G

-- unit s_B; use SUNNY (strict). Closure needed for equality-on-log neighborhood,
-- otherwise portal f/f_au coefficients may see another mask after variation.
theorem engrave (f:E→ℝ) (g:Config G c→ℝ) (h:GaugeInvariant g) (hf:Continuous f)
    (ht:Lease G j p c d a χ) (hk : Reliable G p q)
    (hC: ∀ x∈ball (0:E) d,Boulevard.actual x∈sunny B→ Brush j Y d⁻¹ (fun x=> g (actual x)-(c'+f x)) x)
    (x:E) (hx : ‖x‖<a) (hV : actual x∈sunny B) :
      Brush j (j.factorial*Y) a⁻¹ ((fun U=>g U-(c'+Frame.placed χ p f U)) ∘ actual) x:= by
  let W (y:E) (u:G.El):= g (actual y)-(c'+f (convertLinks χ p u (actual y)))
  have hI y:Continuous (W y):= by
    have he (z):convertLinks χ p z (actual y)=adj z (convertLinks χ p 1 (actual y)):= by simpa only [mul_one] using motion hk (χ:=χ) 1 z (actual y)
    have hy (v:G.El): W y v = g (actual y)-(c'+f (adj v (convertLinks χ p 1 (actual y)))):= by unfold W; exact congr_arg (fun z=>g (actual y)-(c'+f z)) (he v)
    rw [funext hy]; exact continuous_const.sub (continuous_const.add (hf.comp (adj_el _)))
  let V: Set E:= (actual ⁻¹' sunny B) ∩ ball 0 a
  have hc:Continuous (actual (c:=c) (G:=G)):= continuous_pi fun k=> by unfold Boulevard.actual; simp_rw [Work.F03.represent_link]; fun_prop
  have hY:V∈𝓝 x:= IsOpen.mem_nhds ((hc.isOpen_preimage _ (sky B)).inter isOpen_ball) (show x∈V from ⟨hV,mem_ball_zero_iff.mpr hx⟩)
  let b:=(j.factorial:ℝ)*Y
  have hh (y:E) (hy:y∈ V) (u:G.El) : Brush j b a⁻¹ (fun x=> W x u) y:=by
    let f' : E→E:=convertLinks χ p u ∘ actual
    have hv : actual y∈ sunny B:=hy.1
    have hz : ‖y‖<a:= mem_ball_zero_iff.mp hy.2
    have hp:= ht.books y hz u
    have hw : actual (f' y)=chainT u (actual y):= hp.self_of_nhds
    have hk : actual (f' y)∈ sunny B:= by
      rw [hw]; intro i; unfold chainT root; simp only [face_gauge,chord_conj]; exact hv i
    obtain ⟨hE,hA⟩:= ht.arcs y hz u
    let f'' (x:E):= g (actual x)-(c'+f x)
    apply (cascade (g:=f'') hA (hC (f' y) (mem_ball_zero_iff.mpr hE) hk) ht.fine).shimmy
    filter_upwards [hp] with t hp; change actual (f' t)=_ at hp; change g _-(c'+f (f' t))=g (actual (f' t))-_ ; rw [hp]; unfold chainT root; simp only [h ..]; rfl
  obtain ⟨hs,hv⟩:= Meristem.points W G.probHaar ⟨(fun _=>_),integrable_const _,(by filter_upwards [hY] with y hy using (show ∀ i, Brush j (b*(1+a⁻¹)^j) 1 (fun t=> W t i) y from fun i=> (hh y hy i).trim))⟩ (Eventually.of_forall fun y=> (hI y).measurable)
  apply (hs.buds (fun _=>b) (integrable_const _) (inv_pos.mpr ht.ok).le (by simp : (∫ _:G.El,b ∂G.probHaar) ≤ b) (ae_of_all _ (hh x (mem_of_mem_nhds hY)))).shimmy
  refine Eventually.of_forall (fun i=>?_); change g _-(c'+Frame.placed χ p f _) = ∫ v:G.El, g (actual i) - (c'+ f (convertLinks χ p v _)) ∂_; rw [meansRead hk];
  have hg : Continuous (fun v:G.El=> f (convertLinks χ p v (actual i))):= by
    have he (v:G.El): f (convertLinks χ p v (actual i))= g (actual i)-W i v-c':= by unfold W; ring
    simp_rw [he]; exact (continuous_const.sub (hI i)).sub continuous_const
  have hk':= hg.integrable_of_hasCompactSupport (μ:=G.probHaar) (HasCompactSupport.of_compactSpace _)
  rw [integral_sub (integrable_const _) (show Integrable (fun v=> c'+f (convertLinks χ p v (actual i))) G.probHaar from (integrable_const c').add hk'), integral_add (integrable_const _) hk']
  simp
end YM.LocalLTE.Frame
