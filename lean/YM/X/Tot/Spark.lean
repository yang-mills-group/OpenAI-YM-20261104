import YM.X.Tot.Final
/-!
# Dust from local valuations F, exponential confidence ∀warm. Need for approximate integration; no assumptions on rates of Ward-Cluster purchase. Splot horizon selected.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Tot
open Lattice Wilson Next.Rank Normal MvPolynomial Function Filter Set MeasureTheory Asymptotics
open PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Reed Shelf
open Stems hiding X
open Ocean Haze Fielding Print Fund Tri Plate LiftMark Hinge Bare Pulse Labels Pert.RawLabels Crystal Gravity
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge} {F: Labels.Frames G} {d k:ℕ} {V I:Type*} {r R:ℝ} {n:Side}
variable (q:ℕ+)(χ:Floor R)
local notation "Q"=> qu q G
local notation "Ω"=> Foam G
variable (x y z:Fielding.Walk) (p p' a a' b b': Foam G)
local notation "Θ"=> (Reed.Horizontal G)
lemma ill_top {A:Foam G}(h:A∈ Ready q (⊤: Submodule ℝ (Fan G))) (hq:1<q.val)(hr:0<r): Apt q r A:= by
    induction h using Submodule.span_induction with
    | mem i hp=>
       obtain ⟨l,g,h,hX,hY,rfl⟩:=hp; clear hX hY; refine Plate.Apt.up (?_ : Plate.Apt q r (textA q l)) _ h; -- as illA
       refine ⟨⟨l.length,fun i=>by rw [←leafy.mp (echelon q l i)]; exact Heat.Top.cut_bound l.length _⟩,fun P hp=>?_⟩; induction l with
       | nil=> simp_rw [Tot.empty,Pi.one_apply,map_one]; exact constell 1
       | cons a l IH=> simp_rw [text_cons,Pi.mul_apply,map_mul]; apply breaths _ IH; simp_rw [credit,carbon,normF,flatL, map_smul]; apply Released.lin Complex.ofRealCLM.toLinearMap; have he:= hp.later a.k a.x a.order 0 (by rw [norm_zero]; exact hr.le) (fun _:ℕ=>0) (plot.constant hq 0); simp_rw [leads_zero] at he; exact he
    | zero=> refine ⟨⟨0,fun i=> Plate.duty.zero⟩, fun m h=>?_⟩; simp only [Pi.zero_apply,map_zero]; exact Released.zero
    | add a c _ _ x y=> exact x.add y
    | smul a m _ h=> exact h.up (fun _=> a) (constell a) -- defeq
lemma gather_add : gather q x y z (p+p') a b=gather q x y z p a b + gather q x y z p' a b:= by ext1 i; simp only [gather,Pi.add_apply,map_add,tri_plus]
lemma gather_up (c:ℕ→ℂ): gather q x y z (c • p) a b=c*gather q x y z p a b:= by ext1 i; unfold gather;rw [show (c • p) i = c i • p i from rfl,map_smul,tri_scale];rfl
lemma gather_fin (f:I→Foam G) (w:Finset I): gather q x y z (∑ i∈w,f i) a b=∑ i∈w,gather q x y z (f i) a b:= by ext1 i; simp only [gather,Finset.sum_apply,map_sum,tri_sum]
lemma gather_sub : gather q x y z (p-p') a b=gather q x y z p a b - gather q x y z p' a b:= by nth_rw 2 [←sub_add_cancel p p']; rw [gather_add,add_sub_cancel_right]
lemma gather_sym : gather q x y z p a b=gather q y z x a b p:= by ext1 i; unfold gather; rw [tri_spin]
lemma gather_swap : gather q x y z p a b=gather q x z y p b a:= by ext1 i; unfold gather; rw [tri_C]
lemma gather_s : gather q x y z p a b=gather q y x z a p b:= by rw [gather_sym, gather_swap (p:=a)] -- binder
local notation "Fⅰ"=>fades ℂ
local notation "G₀"=> gather q x y z
local notation "Bl"=> Billboard G q
variable (h:Geom q r x y z)(hr:r>0)(hq:1<q.val)
include hq
lemma epi_d (p:ℕ→ℂ)(h:Released p): epi q 1 * p ∈ fades ℂ:= by
    obtain ⟨p',h'⟩:=h; have he : Tendsto (epi q 1) atTop (𝓝 0):= by unfold epi; simp_rw [zpow_one]; exact Complex.continuous_ofReal.continuousAt.tendsto.comp (paths hq).cutoff
    simpa only [zero_mul] using! he.mul h'
include h hr
lemma get_ash (hp:p∈Ash q (⊤: Submodule ℝ (Fan G)))(ha:a∈Ready q Θ)(hb:b∈Ready q Θ): G₀ p a b∈ fades ℂ:= by
     change zoomA q (-1) p∈ Ready q (⊤:Submodule ℝ (Fan G)) at hp; nth_rw 1 [← zoom_back (q:=q) p]; rw [zoom_pose,gather_up]; exact epi_d q hq _ (g_cost x y z _ a b h hr hq (ill_top q hp hq hr) ha hb) -- arg order
lemma ash_second (hp:Apt q r p) (ha:a∈ Ash q Θ)(hb:b∈Ready q Θ): G₀ p a b∈ fades ℂ:= by
    change zoomA q (-1) a∈ Ready q Θ at ha; rw [gather_s]; nth_rw 1 [← zoom_back (q:=q) a];rw [zoom_pose,gather_up,gather_s (x:=y)]; exact epi_d q hq _ (g_cost x y z p _ b h hr hq hp ha hb)
def priceF (q:ℕ+)(χ:Floor R)(x y z:Fielding.Walk)(p a b:Foam G)(L: Billboard G q): ℕ→ℂ:= bill q x y z χ (cloak q x p) (cloak q y a) (cloak q z b) L
local notation "S₀"=> priceF q χ x y z
omit h hr hq
lemma price_c (L:Billboard G q): S₀ p a b L=priceF q χ y z x a b p L:= bill_rotate ..
lemma price_add (L:Bl) : S₀ (p+p') a b L=S₀ p a b L+S₀ p' a b L:= by unfold priceF; rw [map_add,bill_add]
lemma price_s (c:ℕ→ℂ)(L:Bl):S₀ (c • p) a b L=c* S₀ p a b L:= by unfold priceF; rw [cape_p,bill_sc]
include h hq
lemma ash_full (hR:R<r)(hp:p∈Ash q Θ)(ha:a∈ Ready q Θ)(hb:b∈ Ready q Θ) : S₀ p a b (EngineP q G)∈ fades ℂ:= by
     change zoomA q (-1) p∈ Ready q Θ at hp; nth_rw 1 [← zoom_back (q:=q) p]; rw [zoom_pose,price_s]; refine epi_d q hq _ (bill_cost q x y z χ _ _ _ _ (shape_health hq) (launch_ q _ _ x _ hp) (launch_ q _ _ y _ ha) (launch_ q _ _ z _ hb) h hq hR)
end YM.PositionX.Tot
