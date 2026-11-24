import YM.Frontier6.Exact.CostStep

/-! Moving real lengths on all rays; estimates uniform including projection ties. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6
open Function Filter Set Lattice Wilson RG Source Labels MergeProof MergeProof.Ribbons Next.UVStress
open Bid Spec Analysis Table Extraction.Lease Cells Extraction.Around OS Word MeasureTheory Org Canvas Platform
open Next.Extract Dash PhysicalNext.Repeat.Legato MergeProof.Acme
open scoped Topology InnerProductSpace BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{F:Extraction.Order} {S:Table C.book}
variable (K:Final C F S){D d b N w:ℕ}
variable {H:Table C.book}{M:ℕ→Table C.book}{Q:Bin H}{Y:DiffPlan S} (h:Base C F H M Q S Y) (hp:PairProducer C) (hg:G.Simple) (hW:Extraction.Wcmain C)(hG:Grill C F)
set_option quotPrecheck false
local notation "R"=> fuga C.path.levels
variable (B:S.Field d)(P:S.Field b) {I:Type*}[Fintype I]{n:I→ℕ}(v:Tuple S n)
variable {r A ε g:ℝ}(hr:0 < r)(ha:0 ≤ A)(hx:0 < g)(hε:0 < ε)

lemma shells_to_interval {P:ℝ→Prop}{B:ℕ→ℝ}(hp:Note C.S B (-1))(he:∀ᶠ m:ℕ in atTop,∀ r:ℝ,B (m+1) ≤ r → r ≤ B m → P r): ∀ᶠ r:ℝ in 𝓝[>] 0, P r:=by
    obtain ⟨k,h⟩:= eventually_atTop.mp he
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (gt_mem_nhds (hp.pos k))] with r hr hk
    have hv: ∃ i:ℕ, k ≤ i ∧ B i ≤ r:= ((eventually_ge_atTop k).and ((hp.thins (by norm_num)).eventually (ge_mem_nhds (show 0 < r from hr)))).exists
    obtain ⟨hm,hh⟩:= Nat.find_spec hv
    change B (Nat.find hv)≤ r at hh
    let i:= Nat.find hv; change _ ≤ i at hm; have he:k < i:=by
       apply lt_of_le_of_ne hm; intro h'; apply hk.not_ge; exact h'.symm ▸ hh
    apply h _ (by omega : k ≤ i-1) r
    · rw [Nat.sub_add_cancel (by omega:1 ≤ i)]; exact hh
    exact le_of_lt (lt_of_not_ge fun hz=> Nat.find_min hv (by omega : i-1 < i) ⟨by omega,hz⟩)

include h hp hg hW hG hx hr ha hε
lemma seam_dual (k:ℕ)(hk:C.ref w≤ k): ∀ᶠ a:ℝ in 𝓝[>] 0, ∀ (x:E4), ‖x‖=a→ ∀ (y:Seen n),shapes r y→ noSeam C.S k g y→ ∀ (u:I→StateIndex K)(c:I→ℂ), (∀ p,‖c p‖≤ A) → kills K v y u c w →
    ‖listen K B P v y u c x‖ ≤ a^((w:ℝ)-d-b-ε):=by
   let σ:ℝ:= (d:ℝ)+b+8; have hS:0 < σ:=by unfold σ; positivity
   obtain ⟨s,hs,hE,hD⟩: ∃ s:ℝ, 1 < s ∧ s*((d:ℝ)+b)+8*(s-1)< d+b+ε/2 ∧ 1/16+s*((d:ℝ)+b)+8*(s-1)<1/8+(d:ℝ)+(b:ℝ) := by
      let p:=(min (ε/2) (1/16))/σ; have he:0 < p:= div_pos (lt_min (by linarith) (by norm_num)) hS; obtain ⟨y,hu,hv⟩:= exists_between he
      have hx:= (lt_div_iff₀ hS).mp hv; obtain ⟨hd,hD⟩:= lt_min_iff.mp hx; unfold σ at hd hD; exact ⟨1+y,by linarith,by linarith only [hd],by linarith only [hD]⟩
   obtain ⟨j,hj,hb,hJ⟩:= trapeze C.S s hs C.path.levels.fits.mesh
   let e':=(d:ℝ)+(b:ℝ)-(w:ℝ)+ε/2; let f(i:ℕ):=Real.exp (e'*C.S.scale i); have hP: Note C.S f e':= Note.bell_exp ..
   obtain ⟨N,hN⟩:= contour_cost K hp hg hG B P v hs hj hJ hr ha hP
   obtain ⟨a,ha',hA⟩:= mars N; let p:=(w:ℝ)-d-b-ε; have h':=fugaPitch hp hg;let Z := (R)
   have hz := h'.scales C.path.levels.fits.mesh
   have ht:= hP.mills (Note.notes C.S a ha'); have hf:e'+0 < p*(-1):= by unfold e' p; linarith only [hε]
   have hr':= (Note.notes _ (arm N) (arm_pos N)).mills ((Note.note_a C.S).relay j hj hJ)
   refine shells_to_interval h' (?_)
   filter_upwards [ht.outweigh (hz.powr p) hf, ht.outweigh (h'.powr p) hf,hr'.outweigh (hz.splits (Note.notes _ 128 (by norm_num))) (by linarith), hN, slide_exits hp hg hr, grid_dual K B P v h hp hg hW hG ha hx hr hs hE hD (by norm_num) k hk hb hj hJ] with m hx0 hx1 hT hX hM hC r' hm hn x hp' y hy ho u c he he'
   have hr':0 < r':= (hz.pos m).trans_le hm; let a':= C.S.a (j m)
   have hS (x:E4)(ht:x∈arena r')(j:I): Points.cons x (Points.cons 0 (y j))∈conf _:= slide_conf C.S _ (hM r' hm hn x ht _ _ (hy j))
   have hZ(u:E4)(ht:u∈arena r'): u∈ {x:E4| Z (m+1)/16 ≤ ‖x‖ ∧ ‖x‖≤4* Z m}:= ⟨le_trans (by linarith only [hm]) ht.1.le,le_trans ht.2.le (by linarith only [hn])⟩
   refine le_trans (hA r' a' (f m) (C.S.a_pos _) (hP.pos m) (le_trans hT (by linarith only [hm])) (listen K B P v y u c) (fun z ht hv=> hC _ (hZ z ht) hv y hy ho (hS z ht) u c he he') (fun i x hi=> hX r' hm hn y hy u c he i x hi) x (?_)) ?_
   · constructor <;> linarith only [hr',hp'] -- annulus
   rcases le_or_gt 0 p with h|h; exact hx0.trans (Real.rpow_le_rpow (hz.pos m).le hm h)
   exact hx1.trans (Real.rpow_le_rpow_of_nonpos hr' hn h.le)
end YM.Frontier6
