import YM.X.Tot.Lack
/-!
# Sparse contacts. Exact finite peri covariance in open colored monomial ranks. p,B,C arbitrary alphabet. -/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Tot
open Lattice Wilson Next.Rank Normal MvPolynomial Function Filter Set MeasureTheory Asymptotics
open PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Reed Shelf
open Stems hiding X
open Ocean Haze Fielding Print Fund Tri Plate LiftMark Hinge Bare Pulse Labels Pert.RawLabels Crystal Gravity
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge} {q:ℕ+} {d k m:ℕ} {V I:Type*} {r:ℝ}
variable (x y z:Fielding.Walk)(T S:Set (Marks G))
local notation "F₀"=> (fades ℂ)
local notation "Gτ" => gather q x y z
variable (p a b: Foam G) {X Y:Set ℕ}
lemma green_lit (Q:ChaseR)(hu: Usual Q)(h:∀ l:List (Marks G),(∀ i∈l,i∈T)→l.length∈X → gather q x y z p (textA q l) b∈ Q)(he:a∈ Page q X T): Gτ p a b∈ Q:= by
    induction he using Submodule.span_induction with
    | mem i hi=> obtain ⟨l,f,hf,hl,hv,rfl⟩:=hi; rw [gather_s,gather_up,gather_s q y]; exact hu _ _ hf (h l hl hv)
    | zero=>rw [show gather q x y z p 0 b=(0:ℕ→ℂ) from funext fun i=>by simp [gather]]; exact Submodule.zero_mem _
    | add a b _ _ t u=> rw [gather_s,gather_add];simp_rw [gather_s q y x z];exact Q.add_mem t u
    | smul c a _ h=>rw [gather_s,show c • a= (fun _:ℕ=>c) • a from rfl,gather_up,gather_s q y]; exact hu _ _ (constell c) h
lemma lack (h:Apt q r p)(ht:a∈ Page q X T)(hh:b∈Page q Y S)(hb:heightY p d)(hs:∀i∈X,∀ j∈Y,d < i + j)(hg:Geom q r x y z)(hr:0<r)(hq:1<q.val)(hl:Lined q T S y z): gather q x y z p a b∈F₀:= by
    apply green_lit (Q:= F₀) _ _ _ T p a b usual_fading _ ht; intro v hv hw; rw [gather_swap]; apply green_lit (Q:=F₀) _ _ _ S p b _ usual_fading _ hh; intro u he hh; rw [gather_swap]; exact Lack x y z v u hg hr hq h hb (hs _ hw _ hh) fun i hi j hj=> hl i (hv i hi) j (he j hj)
section algebra
variable (Q:Symmetric V)(M P:poly V) (u v w x y z:V→₀ℂ)
local notation "E"=> tri Q
local notation "κ"=> edge Q
lemma single_val : tri Q (glyph x) 1 1=0:= by nth_rw 1 [← mul_one (glyph x)]; rw [tri_cross]; simp
lemma tri_Cp (d:ℂ): E (MvPolynomial.C d*M) P 1=d • E M P 1:= by rw [C_mul'];exact tri_scale ..
lemma chop₁ : tri Q (glyph x) M P= E 1 (κ x M) P+ E 1 M (κ x P):= by nth_rw 1 [← mul_one (glyph x)]; rw [tri_cross]
lemma plain₀ (A:poly V)(v:V→₀ℂ)(h:duty A 0): tri Q 1 A (glyph v)=0:= by nth_rw 1 [tri_rotate]; rw [chop₁]; have hh: edge Q v A=0:= slit_null _ h; simp [hh]
lemma arcStone : κ x (glyph y*glyph y)= 2 • (treats Q x y • glyph y):= by rw [Derivation.leibniz]; simp [link,C_mul', mul_comm (glyph y) (C _),two_smul]
lemma milestone (h:treats Q x y=0): κ x (glyph y * glyph y)=0:= by rw [arcStone,h,zero_smul,smul_zero]
lemma bandit (h:treats Q x v=0 ∨ treats Q y v=0): κ y (κ x (glyph v*glyph v))=0:= by
    rcases h with h|h
    · rw [milestone Q _ _ h,map_zero]
    rw [show κ y (κ x _)=κ x (κ y (glyph v*glyph v)) from slit_slit .., milestone Q _ _ h,map_zero]
lemma band_left (a b c:V→₀ℂ)(hx:treats Q a u=0∨ treats Q b u=0)(hy:treats Q b u=0∨ treats Q c u=0)(hz:treats Q a u=0∨ treats Q c u=0) : multi Q (glyph u*glyph u) (Tot.triple a b c)=0:= by rw [Tot.triple,m3]; simp only [bandit Q u a b hx,bandit Q u b c hy,bandit Q u a c hz,map_zero,mul_zero,add_zero] -- replace
lemma solitary (A:poly V)(t:V→₀ℂ)(u:V→₀ℂ)(h:duty A 0) : E 1 A (κ u (glyph t*glyph t))=0:= by rw [arcStone]; simp [← Nat.cast_smul_eq_nsmul ℂ (2:ℕ), tri_scale₂, plain₀ Q A t h]
lemma burden (A:poly V)(h:duty A 2)(hx:treats Q x v=0∨ treats Q y v=0)(hy:treats Q y v=0∨ treats Q z v=0)(hz:treats Q x v=0∨ treats Q z v=0): E (Tot.triple x y z) A (glyph v *glyph v)=0:= by
    have he(a b:V→₀ℂ):duty (edge Q b (edge Q a A)) 0:= slit_budget _ (slit_budget (k:=1) _ h)
    rw [Tot.triple]; simp only [tri_cross,chop₁ ,bandit Q v _ _ hx,bandit Q v _ _ hy,bandit Q v _ _ hz,solitary Q _ v z (he x y), solitary Q _ v y (he x z), solitary Q _ v x (he y z), show κ z (κ y (κ x A))=0 from slit_null _ (he _ _), map_zero,tri_z₁,tri_z₂,add_zero]
end algebra
end YM.PositionX.Tot
