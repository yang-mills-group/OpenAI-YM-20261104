import YM.X.Pulse.Twice
/-!
# reality, Unit and Signed spin of unheated stencil α families. independent of ℒ
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Pulse
open Lattice Wilson Next.Rank Normal MvPolynomial Function Filter Set MeasureTheory Asymptotics Reed Braid
open Clove Crystal Gravity Shelf Haze Ocean Interval Size Fielding Print PertExtension LatticePT Plate
open Stems hiding X
open Crate Crate.Fund Hinge Spindle
open scoped Topology ContDiff BigOperators Classical
variable {q:ℕ+}{n:Side}{k d:ℕ}{R:ℝ}{I V T:Type*}{G:Gauge}
open Pert.Position Maxwell Maxwell.Free Bare Function Pert.RawLabels
variable {F:Labels.Frames G}(S:Bare.Shop F) (w:Floor R)
local notation "E"=> Pert.Position.E F
local notation "A"=> F.level d
local notation "L"=> Labels.Label G d
local notation "E₀"=> epsilon q k
variable (Y:T→ℕ)
open Finset
variable {e:ℝ}(P:Fin k→Word G)
variable {j m:ℕ}(x:Fin m→ Site n)
local notation "Z"=> poly (Jam n G)
variable (s:Signed)(p:Fin m→ Pert.Position.E F d)(e₀:ℝ)
local notation "Px" b=> partM S n e₀ x d b
set_option quotPrecheck false
local notation "R₀"=> (Model F).conj (hierarchy F).spin d
local notation "sρ"=> Pert.Rigid.wear F d
local notation "U₀"=> Module.End ℂ (E d)
def α_c (f:U₀): U₀:= (R₀).comp (f.comp R₀)
-- cancellation and move lenses
def α_s (f:U₀): U₀:= sρ (s⁻¹) ∘ₗ f ∘ₗ sρ s
lemma crρ (v:E d) : R₀ (R₀ v)=v:= by simp
lemma sρ_mul(h u:Signed)(v:E d) : (sρ h) (sρ u v) = (sρ (h*u)) v:= (Table.mirror_mul (Model F) ..).symm
lemma sρ_back (v:E d): (sρ s) ((sρ (s⁻¹)) v)= v:= by rw [sρ_mul,mul_inv_cancel]; exact Table.mirror_one ..
lemma sρ_real (v:E d) : (R₀) ((sρ s) v)= sρ s (R₀ v):= Table.mirror_star ..
variable (f:Module.End ℂ (Pert.Position.E F d))
-- iteration eq
lemma orbit_rev : passV (α_s s f) (Px 0) p= passV f (partM S n e₀ (s.act ∘ x) d 0) ((sρ s) ∘ p):=by
    simp only [pass_view]; apply Finset.sum_congr rfl; intro i _; rw [← part_signed S x e₀ s, YM.PositionX.map_update,α_s]; simp only [comp_apply,LinearMap.comp_apply,sρ_back]
lemma orbit_star : passV (α_c f) (Px 0) p=star (passV f (Px 0) (R₀ ∘ p)):= by
    simp only [pass_view,star_sum]; apply Finset.sum_congr rfl; intro i _; rw [← part_star S x e₀,YM.PositionX.map_update]; rw [show (R₀) ∘ (R₀∘p) = p from funext (fun i=> crρ (p i))]; rfl -- f input update
variable {f}
variable (y:Fin m → Fielding.Walk)(z:Fin m→E4)(hy:∀ i,plot q (y i) (z i)) {r:ℝ}(he:Porch.Apart Finset.univ z r)(hr:R<r)(t:∀ i:ℕ,Site (side q i))(hq:1<q.val)
lemma post_s : s.act ∘ postal y (t k) k = postal (fun i=> s.act ∘ y i) (s.act (t k)) k:= by funext i; simp [postal,stock] -- lemma wrap_signed simp 
lemma plot_s (v:E4)(z:Fielding.Walk)(h:plot q z v) : plot q (s.act ∘ z) (s.ortho.motion v):= (s.ortho.motion.continuous.continuousAt.tendsto.comp h).congr fun i=> (spot_s s ..).symm
variable {L₀:ℕ→ Module.End ℂ (Pert.Position.E F d)}
lemma balance_s (hb:balance q S r m L₀):balance q S r m (α_s s ∘ L₀):= by
    intro y z hy he t p; let u:= fun i=> s.act ∘ y i; let v:= s.ortho.motion ∘ z; have hv:Porch.Apart Finset.univ v r:= by intro i hi j hj hn; unfold v; rw [comp_apply,comp_apply,← map_sub,LinearIsometryEquiv.norm_map]; exact he _ hi _ hj hn -- explicit .motion
    let P:= sρ s ∘ p; obtain ⟨C,hC⟩:= hb u v (fun i=> plot_s s _ _ (hy i)) hv (fun i=>s.act (t i)) P; refine ⟨C,hC.congr ?_⟩; intro k; unfold P u; simp only [MultilinearMap.sub_apply]; rw [show (α_s s ∘ L₀) k=α_s s (L₀ k) from rfl,orbit_rev,← post_s (t:=t) s y, part_signed] -- unfolding
lemma balance_r (hb:balance q S r m L₀):balance q S r m (α_c ∘ L₀):= by
    intro y z hy he t p; obtain ⟨C,hc⟩:= hb y z hy he t (R₀ ∘ p); refine ⟨star C,(hc.star).congr ?_⟩; intro i;simp only [MultilinearMap.sub_apply,star_sub,part_star,star_star]; rw [show (α_c ∘ L₀) i=α_c (L₀ i) from rfl,orbit_star]
section path
-- average lemmas generic
variable {I:Type*}{c:I→ℂ}{s':Finset I}{J:I→ℕ→ Module.End ℂ (Pert.Position.E F d)}
lemma balance_avg (hw:∀ i∈s', balance q S r m (J i))(hb:∑ i∈ s',c i=1): balance q S r m (fun k=>∑ i∈s',c i • J i k):=by
    intro y z hy he t p; let T (b i):= partM S (side q i) (epsilon q i) (postal y (t i) i) d b; let f(i:ℕ)(j:I) := c j • (T 1 i -passV (J j i) (T 0 i)) p; have hf : Released (fun i=> ∑ j∈ s',f i j):= Released.sumR _ (fun j hj=> Shelf.breaths (constell _) (hw j hj y z hy he t p)) -- smul eq mul
    apply Eq.mp ?_ hf; congr 1;ext1 i; have he' : ∑ j∈s', c j • passV (J j i) (T 0 i) p= passV (∑ j∈s',c j • J j i) (T 0 i) p:= by simp only [pass_view, LinearMap.sum_apply, LinearMap.smul_apply, MultilinearMap.map_update_smul, MultilinearMap.map_update_sum,Finset.smul_sum]; rw [Finset.sum_comm]
    unfold f; simp only [MultilinearMap.sub_apply,smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul,he',hb,one_smul]; rfl
end path
end YM.PositionX.Pulse
