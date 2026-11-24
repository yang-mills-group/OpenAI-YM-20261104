import YM.X.Sage.Words
/-!
# one-rung FO valuation assessment ∼ all horizon. Supports deterministic Repo.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Sage
open Lattice Wilson Next.Rank Normal LiftMark PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Shelf Tot
open Filter Function Reed Ocean Hinge Haze Fielding Print Tri Plate Gravity Chir
open Stems hiding X
open MvPolynomial Set

open scoped Topology BigOperators Classical
variable {G:Gauge} {m d k:ℕ} {V:Type*} {q:ℕ+} {r R:ℝ}
local notation "L"=> (atTop:Filter ℕ)
local notation "U"=> G.ColorIndex
local notation "K"=> Reed.Horizontal G
local notation "Θ"=> (⊤:Submodule ℝ (Fan G))
local notation "Ω"=>Foam G
variable {S:Submodule ℝ (Fan G)} {p v:Foam G} {X:Set (Bone G S)}
abbrev single (q:ℕ+)(d:ℕ)(T:Set (Bone G S)):= Page q {d} T
lemma story (a b:List (Bone G S)): textA q (a++b)= textA q a*textA q b:= by induction a with| nil=> simp| cons i a ih=> simp [ih,mul_assoc]
lemma single_mul (h:p∈single q d X)(ht:v∈ single q k X): p*v∈single q (d+k) X:= by
    induction h using Submodule.span_induction with
    | mem i hi=>
        obtain ⟨l,u,hu,hl,hX,rfl⟩:=hi; induction ht using Submodule.span_induction with
        | mem j hj => obtain ⟨l',u',hu',hl',hp,rfl⟩:=hj; rw [mul_comm,foamX,mul_comm,foamX, ←story,smul_smul]; exact page_live _ _ _ _ (breaths hu hu') (fun i h=> List.mem_append.mp h|>.elim (hl i) (hl' i)) (by have h:l.length=d:=hX; have hz:l'.length=k:=hp; simp [h,hz])
        | zero=> simp
        | add a b h g t u=> rw [mul_add]; exact Submodule.add_mem _ t u
        | smul a m _ h=> rw [mul_smul_comm]; exact Submodule.smul_mem _ _ h
    | zero=>simp
    | add a b _ _ t u=> rw [add_mul]; exact Submodule.add_mem _ t u
    | smul a m _ h=> rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ h
lemma ce_top (B:Tops G): credit q B ∈ single (S:=Θ) q 1 Set.univ:= credit_lean q _ B (mem_univ _) rfl
lemma ce_step (B:Marks G):credit q B∈ single (S:=K) q 1 Set.univ:= credit_lean q _ B (mem_univ _) rfl
lemma single_ready (h:p∈single q d X): p∈Ready q S := home_close q X (subset_univ _) (subset_univ _) h
variable (i:Tet) (a:G.ColorIndex)
lemma step_up : ξ q r i a∈ single q 1 Set.univ (S:=Θ):= ce_top (upMark (Chir.spin r i a)) -- notation `S` argument late?
lemma single_mulK (hm:m=d+k)(h:p∈single q d X)(ht:v∈single q k X): p*v∈single q m X:= hm.symm ▸ single_mul h ht
lemma foame_ready (w:PlaqAxes) : foame q w a∈ single q 2 Set.univ (S:=Θ):= by
    unfold foame
    refine (single (S:=Θ) q 2 Set.univ).sum_mem ?_
    intro j _
    refine (single (S:=Θ) q 2 Set.univ).sum_mem ?_
    intro k _
    apply (single (S:=Θ) q 2 Set.univ).smul_mem
    exact single_mulK (m:=2) (d:=1) (k:=1) rfl (p:=topA q w.val.1 j) (v:=topA q w.val.2 k) (ce_top (q:=q) (columnA w.val.1 j)) (ce_top (q:=q) (columnA w.val.2 k))
lemma comp_ready (r:ℝ): bcomp q r i a∈ single (S:=Θ) q 2 Set.univ:= by rw [compb]; refine (single (S:=Θ) q 2 Set.univ).sum_mem ?_; intro j _; exact (single (S:=Θ) q 2 Set.univ).smul_mem _ (foame_ready a j)
local notation "Sτ"=> single (S:=K) q
lemma degreeP0 {r:ℝ} : ξ q r i a ∈ Sτ 1 Set.univ:= ce_step _
-- restrict by endpoint sign (for rank bookkeeping)
def terminals (G:Gauge)(r:ℝ): Set (Marks G):= {z| ∃(i:Tet)(x:G.ColorIndex),z=Chir.spin r i x}
lemma degreeΦ : ξ q r i a ∈ single (S:=K) q 1 (terminals G r):= credit_lean _ _ _ (by exact ⟨i,a,rfl⟩) rfl
lemma degreeU : μDeck q G∈ single q 2 (terminals G (-1)):= by
    rw [tune_deck]
    refine (single (S:=K) q 2 (terminals G (-1))).sum_mem ?_
    intro i _
    refine (single (S:=K) q 2 (terminals G (-1))).sum_mem ?_
    intro j _
    exact single_mulK (m:=2) (d:=1) (k:=1) rfl (degreeΦ (r:=-1) (q:=q) i j) (degreeΦ (r:=-1) (q:=q) i j)
lemma degreeB : βDeck q G∈ single q 3 (terminals G 1):= by
    rw [ward_deck]
    unfold cubicP
    refine (single (S:=K) q 3 (terminals G 1)).sum_mem ?_
    intro i _
    refine (single (S:=K) q 3 (terminals G 1)).sum_mem ?_
    intro j _
    refine (single (S:=K) q 3 (terminals G 1)).sum_mem ?_
    intro k _
    exact (single (S:=K) q 3 (terminals G 1)).smul_mem _ (single_mulK (m:=3) (d:=1) (k:=2) rfl (degreeΦ (q:=q) (r:=1) 0 i) (single_mulK (m:=2) (d:=1) (k:=1) rfl (degreeΦ (r:=1) (q:=q) 1 j) (degreeΦ (r:=1) (q:=q) 2 k))) -- infer ℕ
lemma h_stride : μLift q G ∈ single (S:=Θ) q 3 Set.univ:= by
    rw [μcrown]
    refine (single (S:=Θ) q 3 Set.univ).sum_mem ?_
    intro i _
    refine (single (S:=Θ) q 3 Set.univ).sum_mem ?_
    intro j _
    exact (single (S:=Θ) q 3 Set.univ).smul_mem _ (single_mulK (m:=3) (d:=1) (k:=2) rfl (step_up (q:=q) (r:=-1) i j) (comp_ready (q:=q) i j (-1)))
lemma b_stride : βLift q G ∈ single (S:=Θ) q 4 Set.univ:= by
    rw [βcrown]
    unfold cubicP
    refine (single (S:=Θ) q 4 Set.univ).sum_mem ?_
    intro i _
    refine (single (S:=Θ) q 4 Set.univ).sum_mem ?_
    intro a _
    refine (single (S:=Θ) q 4 Set.univ).sum_mem ?_
    intro b _
    refine (single (S:=Θ) q 4 Set.univ).sum_mem ?_
    intro c _
    exact (single (S:=Θ) q 4 Set.univ).smul_mem _ (single_mulK (m:=4) (d:=2) (k:=2) rfl (comp_ready (q:=q) i a 1) (single_mulK (m:=2) (d:=1) (k:=1) rfl (step_up (q:=q) (r:=1) (loop i) b) (step_up (q:=q) (r:=1) (ℓ i) c)))
open Heat.Top (cut)
lemma cut_cost (t:poly V)(h:duty t (k+1)): duty (t-Heat.Top.cut (k+1) t) k:= by
    apply Finset.sup_le; intro i hi; rw [mem_support_iff, coeff_sub,Heat.Top.cut_coeff] at hi; by_cases he:Heat.Top.degree i=k+1; simp [he] at hi; rw [if_neg he, sub_zero] at hi; have hx:= le_totalDegree (mem_support_iff.mpr hi); rw [Heat.Top.degree_eq] at he; change (i.sum fun _ k=> k)≤ k; change t.totalDegree ≤ k+1 at h; omega
lemma upperCost (h:heightY p (d+1)): heightY (p-liftCut (d+1) p) d:= fun i=> cut_cost _ (h i)
lemma apt_sub (h:Apt q r p)(ht:Apt q r v): Apt q r (p-v):= by rw [sub_eq_add_neg]; rw [← neg_one_smul ℂ v]; exact h.add (ht.up (fun _=> (-1:ℂ)) (constell _))
-- momentum projection lifting declarations immediate stances on shell
variable {B:Labels.Frames G}(f:Bare.Shop B) (χ:Floor R)
variable (hq:1<q.val) (hk:2*k≤d)
include hq
variable {A:poly (CoverC G)} (h:Hue.Fixed A)(he:Tri.HC A k)(hv:0<k)
local notation "Lτ"=> Tri.crease hk he h
lemma earn₀ (hv:0 < k): stance f q d (crease hk he h) - headP q (2*k) A∈Ash q K:= by
    have hx:=regard f hq (crease hk he h) (creased hk he h) hv; dsimp only at hx; rw [known_price hk he h B f hv] at hx; exact hx
lemma earn₁ (hv:0 < k): liftCut (k+1) (highs q χ f d (crease hk he h))-coronaP q (2*k) A∈ Ash q Θ:= by
    have he' := high_view f χ hq (crease hk he h) (creased hk he h); dsimp only at he'; rw [known_price hk he h B f hv] at he'; exact he'
end YM.PositionX.Sage
