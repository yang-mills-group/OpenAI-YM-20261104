import YM.X.Dial.Tully
/-!
# Primary assemblage linear for labels. Gauge H. No dependence on stencil maps after smoothing.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Dial
open Lattice Wilson Next.Rank Normal MvPolynomial Function Stems Filter MeasureTheory Metric Interval Hinge
open Source PertExtension LatticePT Labels Filter Gauss Jet
open scoped Topology ContDiff BigOperators Pointwise Classical
variable {G:Gauge} {d:ℕ} {F:Labels.Frame G d} (S:SectionData F) {H:Hol G} (s:Signed) (h:S.Sound H) (P:Bid.pop S)
local notation "v"=> F.Coeff
local notation "L"=> Label G d
local notation "W"=> Curly G
local notation "Cₚ"=> topMatrix S H h P
section
variable {V:Type*} [NormedAddCommGroup V][NormedSpace ℝ V]
-- Complex linear convergence jet
lemma chi (h:ℝ→ℂ)(k:ℕ)(s:ℂ): someJ (s • h) k=s • someJ h k:= by unfold someJ;rw [show s • h= _ from (rfl:s • h=(fun t=>s • h t)), iteratedDeriv_const_smul_field s];rw [smul_comm s] -- inspect
lemma ofR (h:ℝ→ℝ)(k:ℕ)(hp:ContDiffAt ℝ (↑k) h 0): someJ (Complex.ofReal ∘ h) k=Complex.ofRealCLM (someJ h k):= by
    unfold someJ iteratedDeriv -- clm
    rw [show Complex.ofReal= ⇑Complex.ofRealCLM from rfl, Complex.ofRealCLM.iteratedFDeriv_comp_left hp le_rfl, map_smul]; -- inspect
    rfl
end

def squareP (n:ℕ)(i:F.Index):= mark (evalS S i) (opt i h P) ((F.grades i).2+n)
def boardP (n:ℕ): F.Coeff→ₗ[ℂ] Curly G where
    toFun c:= ∑ i:F.Index, c i • squareP S h P n i
    map_add' a b:= by simp [Finset.sum_add_distrib,add_smul]
    map_smul' a b:= by simp [Finset.smul_sum,smul_smul]
abbrev squareC (A:Brush G)(c:F.Coeff) : ℝ→ℂ:= fun r=> S.evaluate c (posit (r • A))
def coalition (A:Brush G): v →ₗ[ℂ] ℝ→ℂ where
    toFun:=squareC S A
    map_add' c d:=by funext t;simp [squareC,SectionData.evaluate]
    map_smul' c d:=by funext t;simp [squareC,SectionData.evaluate]
include h in
lemma optics (A:Brush G)(i:F.Index): coalition S A (Pi.single i 1)= Complex.ofReal ∘ along (evalS S i) A:= by funext z; change S.evaluate (Pi.single i 1) (posit (z • A))=↑(evalS S i (posit (z • A))); exact (eval_true i h (posit (z • A))).symm
include h P in
lemma ponder (i:F.Index)(A:Brush G): ContDiffAt ℝ ω (coalition S A (Pi.single i 1)) 0:= by rw [optics S h]; exact Complex.ofRealCLM.contDiff.contDiffAt.comp 0 (along_zero (opt i h P) A)
lemma snapP (n:ℕ)(i:F.Index)(x:Brush G) : Stems.snap x (squareP S h P n i)=someJ (coalition S x (Pi.single i 1)) ((F.grades i).2+n):= by rw [squareP,mark_test,optics S h,ofR _ _ ((along_zero (opt i h P) x).of_le le_top)];rfl
lemma boxPoint (n:ℕ)(p:L)(hq:ℕ×ℕ)(hp:p∈Grade hq) (A:Brush G): Stems.snap A (boardP S h P n (F.coords p))= someJ (coalition S A (F.coords p)) (hq.2+n):= by
    let t(i:F.Index):= (F.coords p i) • coalition S A (Pi.single i 1)
    let j:=hq.2+n; have he: ∑ i:F.Index, t i=coalition S A (F.coords p):=by
       unfold t; simp_rw [← map_smul, ← map_sum]; conv_rhs => rw [← F.basis.sum_repr p, map_sum]
       simp only [map_smul,F.coords_basis];rfl
    have ht: someJ (∑ i:F.Index,t i) j=∑ i:F.Index,(F.coords p i) • someJ (coalition S A (Pi.single i 1)) j:= by
       have hf(i:F.Index):ContDiffAt ℝ (↑j) (t i) 0:= ((ponder S h P i A).of_le (show ↑j≤ω from le_top)).const_smul (F.coords p i)
       have he: someJ (∑ i:F.Index,t i) j= ∑ i:F.Index,someJ (t i) j:= by unfold someJ;rw [iteratedDeriv_sum (fun i _=> hf i),Finset.smul_sum]; -- name
       rw [he]; exact Finset.sum_congr rfl fun i _=> chi .. -- namespace Force conflict
    rw [← he,ht]; simp only [boardP,LinearMap.coe_mk,AddHom.coe_mk,map_sum,map_smul]; apply Finset.sum_congr rfl; intro i _; by_cases hv:hq=F.grades i; · rw [snapP]; unfold j; rw [hv]
    rw [F.power_coefficient i hv hp,zero_smul,zero_smul]
lemma keeps_grade (i:ℕ×ℕ)(p:L)(hp:p∈Grade i)(t:Ortho): tensor t p∈ Grade i:= by have he:= gradePart_mem i (tensor t p); rwa [gradePart_turn,gradePart_self p i hp] at he
lemma boxS (n:ℕ)(c:F.Coeff): relay s (boardP S h P n c)= boardP S h P n (F.act s.ortho c):= by
    obtain ⟨p,rfl⟩:=F.coords.surjective c; rw [F.act_coords]; nth_rw 1 2 [← F.basis.sum_repr p]; simp only [_root_.map_sum,_root_.map_smul]; refine Finset.sum_congr rfl fun i _=> congr_arg _ ?_; let B:=F.basis i; let r:=F.grades i; apply snap_ext; intro x; rw [read_snap, boxPoint S h P n B r (F.pure i), boxPoint S h P n (tensor s.ortho B) r (keeps_grade r B (F.pure i) _)]; apply congr_arg (someJ · _) (funext (fun i=>?_));
    change S.evaluate _ (posit (i • Lbrush s x)) = S.evaluate _ (posit _); rw [← map_smul,← show pull s 0 (posit (i • x))= posit (Lbrush s (i • x)) from land_exp s (i • x), h.Hpart,F.act_coords]
end YM.PositionX.Dial
