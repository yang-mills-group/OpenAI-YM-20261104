import YM.RGComparison01.Marks.Cost
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Pledge
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter Mixed Reserves
open PhysicalNext PhysicalNext.Repeat Packets Art Silica Poll Pond Shield Eider Gas Ursell Trees Height Sail
open PhysicalNext.Repeat.Lotus Team Merge
open AnalyticBridge VerifiedReset Collection Quotes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge} {ι : Type} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : RG.Rep G f}
    {n : ℕ} {W a r σ Λ μ s κ w c' C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
    {H : Cash W s μ L Q o C T R} {d C' A B e δ t D D' v K :ℝ} {j k ℓ:ℕ} {χ:Chi} {Ω : Utopia H j v d r C' χ}
    {Ψ : ℕ → Prop} {x:ℕ→ℝ}
local notation "Z" => H.faresP
local notation "bZ" => H.birth
local notation "TZ" => Tree.Forest S.ratio
variable [Fintype ι]
variable (M:ι→Leaf R) (rA:ι→ℝ)
abbrev raised (H : Cash W s μ L Q o C T R) (p : Cake M H): Support c := H.smallAt p.1
-- M.C.Taxes only on regular log. before force shape
abbrev glaze (Ω:Utopia H j v d r C' χ) (k:ℕ) (e:ℝ) (Y:Head S→ℝ) (i:Cake M H) := (∏ j∈ i.2.val,rA j)*(Palette.team M i.2).whole Ω k e Y i.1.val
abbrev rise (H:Cash W s μ L Q o C T R)(p:Cake M H): Caked M (S:=S):=(p.1.val,p.2)
def sheen (p:Cake M H)(Ψ:ℕ→Prop)(D t D':ℝ):= (∏ i∈p.1.val\ p.2.reach,freight Ψ D t D' i) * Real.exp (Q.mark L μ s * Cash.numP p.1.val) * Real.exp (Q.ε*H.shapeW p.1.val)

omit [Fintype ι] in
lemma sheen_paid (p:Cake M H)(h:1≤D)(ht:1≤t)(he:1≤D'): 1 ≤ sheen M p Ψ D t D':= by
   apply one_le_mul_of_one_le_of_one_le
   · exact one_le_mul_of_one_le_of_one_le (one_le_prod fun _ _=> stock_ge h ht he _) (Real.one_le_exp (mul_nonneg H.laws.acquired.marked (Nat.cast_nonneg _)))
   exact Real.one_le_exp (mul_nonneg Q.usable.le (H.positive_volume _))

omit [Fintype ι] in
lemma sparkled (p:Cake M H)(Ω:Utopia H j v d r C' χ) (k:ℕ)(B:ℝ) (x:ℕ→ℝ) (Ψ:ℕ→Prop) (D t D' e:ℝ) : sheen M p Ψ D t D'*glaze M rA Ω k B (maskRaise Ω Ψ x e) p = B*glorious M H (liftedPay Ω Ψ x e D t D') rA k (rise M H p):= by
   unfold sheen glaze whole glorious eaten; dsimp only [rise]
   simp_rw [Palette.label]
   split_ifs with hp
   · have hM : blaze (p.1.val\p.2.reach)=blaze p.1.val:= by
       ext u; simp only [blaze,Finset.mem_toRight,Finset.mem_sdiff]; rw [and_iff_left]; intro hi; obtain ⟨i,hh,hp⟩:= Finset.mem_image.mp hi; unfold Palette.sign at hp; cases h:(M i).turn <;> simp [h,Wing.badge] at hp
     unfold liftedPay; rw [Finset.prod_mul_distrib, snow,hM]; ring
   ring
-- use Reach hit as Budget.C.Reader. preserves labels
lemma cream (Ω:Utopia H j v d r C' χ) (hd:1≤D) (ht:1≤t) (he:1≤D')(hb:Casing R x Ψ)(hv:0 ≤ e)(hB : 0≤B) (hr:∀ i,0≤ rA i)
   (hq:Ready H.supportP (radiusB s) (tariff (fun i=>liftedPay Ω Ψ x e D t D' i+Tickets.extra (Palette.sign M S) (Palette.wages M rA) i) (stairs H) (tolling H) Q.ε) (Q.exp+2*Q.ε) w Q.δ (1/2))(k:ℕ) : Ac.Hit (raised M H) (radiusB s) (fun p=> sheen M p Ψ D t D'*glaze M rA Ω k B (maskRaise Ω Ψ x e) p) Q.exp (B*(extract Q.ε k 0 0 *treeYield w (1/2) 0)):= by
   have he' := hit_cakes M H (pay_ge Ω hd ht he hb hv) hr hq k
   intro p; have hY : Injective (rise M H):= fun _ _ h=> Prod.ext (Subtype.ext (congr_arg Prod.fst h)) (congr_arg (fun i:Caked M (S:=S)=>i.2) h)
   convert budget_scale hB (budget_pull (rise M H) hY (he' p)) using 1
   ext i; dsimp only; split; next hi=> rw [if_pos (show p∈reaches M H (rise M H i) from hi),sparkled,mul_assoc]; rfl
   next hj=> rw [if_neg (show p ∉reaches M H (rise M H i) from hj),mul_zero]

namespace Baked
-- Ursell family over augmented tuples retains canonical factorial exactly, repeated und multiplicities
abbrev Cl (H : Cash W s μ L Q o C T R):= Clusters (Cake M H)
abbrev seam (H : Cash W s μ L Q o C T R) (x y:Cake M H) := H.seam x.1 y.1
abbrev origins (H : Cash W s μ L Q o C T R) (p:Cl M H) := unionOf (raised M H) p.2
variable (Ω:Utopia H j v d r C' χ)
abbrev debt (p:Cl M H) (k:ℕ) (B:ℝ) (Y:Head S→ℝ):= clusters (seam M H) (fun i=> (2:ℝ)^j *glaze M rA Ω k B Y i) p.2
abbrev weight (w:Cake M H→ℝ) (p:Cl M H) := ∏ i,w (p.2 i)

def Geno (Q:ConnectedActivityE6.Target G P)(j k:ℕ)(w B:ℝ):= 2^j * (B*(extract Q.ε k 0 0*treeYield w (1/2) 0))
-- unweighted table also summable/or.Price
omit [Fintype ι] in
lemma zero_glaze (p:Cake M H) (hB:0≤B) (hx:Casing R x Ψ)(he:0≤e)(h:∀ i,0≤ rA i): 0 ≤ glaze M rA Ω k B (maskRaise Ω Ψ x e) p:= mul_nonneg (prod_nonneg fun _ _=>h _) (Team.whole_nn _ hB (raises _ he hx.nonneg) _)
omit [Fintype ι] in
lemma grain (p:Cl M H) (hB:0≤ B)(hx:Casing R x Ψ)(he:0≤e)(hr:∀ i,0≤rA i): 0 ≤ debt M rA Ω p k B (maskRaise Ω Ψ x e):= clusters_nonneg (seam M H) (fun p=>mul_nonneg (by positivity) (zero_glaze M rA Ω p hB hx he hr)) _
omit [Fintype ι] in
lemma testing (H:Cash W s μ L Q o C T R) : Tests (seam M H) (raised M H) := fun i j=>H.testS i.1 j.1
-- E boost and all mark purchases.
lemma roll (hd:1≤D) (ht:1≤t) (he:1≤D')(hb:Casing R x Ψ)(hv:0 ≤ e)(hB : 0≤B) (hr:∀ i,0≤ rA i)
   (hq:Ready H.supportP (radiusB s) (tariff (fun i=>liftedPay Ω Ψ x e D t D' i+Tickets.extra (Palette.sign M S) (Palette.wages M rA) i) (stairs H) (tolling H) Q.ε) (Q.exp+2*Q.ε) w Q.δ (1/2))(k:ℕ) (hg:0≤a) (hδ:0<δ)
   (hU: a+δ+δ ≤ Q.exp) {v:ℝ} (hV: Geno Q j k w B ≤ v) (hT:0<v) (hy:degreePrice (radiusB s) v δ ≤ 1/2) :
    Ac.Hit (origins M H) (radiusB s) (fun p=> weight M (fun v=> sheen M v Ψ D t D') p * debt M rA Ω p k B (maskRaise Ω Ψ x e)) (a+δ) (v*(1-1/2)⁻¹):= by
   let v' i := ((2:ℝ)^j *glaze M rA Ω k B (maskRaise Ω Ψ x e) i); let f:= (fun p=> sheen M (H:=H) p Ψ D t D'); let F i:= f i * v' i
   have hf i: 0 ≤ F i:= mul_nonneg (zero_le_one.trans (sheen_paid M i hd ht he)) (mul_nonneg (pow_nonneg (by norm_num) _) (zero_glaze M rA Ω i hB hb hv hr))
   have hw : Ready (raised M H) (radiusB s) F (a+δ) v δ (1/2):= by
     refine ⟨hT,hδ,hy,by norm_num,hf,fun i=>?_⟩
     have he := budget_scale (pow_nonneg (by norm_num : 0 ≤ (2:ℝ)) j) (cream M rA Ω hd ht he hb hv hB hr hq k i)
     refine budget_loosen (budget_mono he ?_ (fun x=>?_)) hV
     · intro z; split; exact mul_nonneg (hf _) (Real.exp_nonneg _); exact le_rfl
     · split
       next hx =>
          apply le_trans (mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right hU (Nat.cast_nonneg _))) (hf x)) (le_of_eq ?_); unfold F f v'; ring
       next hn=> rw [mul_zero]
   intro i
   have hh:= log_hit_tail (seam M H) (raised M H) (radiusB s) (testing M H) hw (add_nonneg hg hδ.le) 0 i
   rw [pow_zero,mul_one] at hh; convert hh using 1; ext p
   simp only [Nat.zero_le,true_and]; split; next hp=> apply congr_arg₂ (· * ·) _ rfl; unfold weight debt clusters; simp only [F,f,v', prod_mul_distrib]; ring
   next=> rfl
end Baked
end YM.RGComparison01.Pledge
