import YM.UVExt.JetPacket
/-! Finite differentiation and summability costs for the primal jets. Total term carries volume after probing, not before. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExt.Paths
open Function RG Wilson Precision Exterior Lattice Laurent Bid Filter Real Set Matrix
open scoped ContDiff Topology Classical BigOperators

lemma tag_add (f g : ℝ→ℝ) {q} (h₁ : ContDiff ℝ ∞ f) (h₂ : ContDiff ℝ ∞ g) : tag q (f+g)=tag q f+tag q g := iteratedDeriv_add (h₁.contDiffAt.of_le (finite_cap _)) (h₂.contDiffAt.of_le (finite_cap _))
lemma tag_smul (f : ℝ→ℝ) {q} (h₁ : ContDiff ℝ ∞ f) (c : ℝ) : tag q (c • f)=c*tag q f := iteratedDeriv_const_smul (h₁.contDiffAt.of_le (finite_cap _)) _
lemma tag_sum {α} [Fintype α] (F : α→ℝ→ℝ) {q} (H : ∀ i,ContDiff ℝ ∞ (F i)) : tag q (∑ i,F i)=∑ i,tag q (F i) := iteratedDeriv_sum (fun i _=>(H i).contDiffAt.of_le (finite_cap _))

variable {G : Gauge} {W : Shadow G} {p : Clip} {C σ Λ : ℝ} {n : Side}

local notation "⨳" => ((Fintype.card Signed:ℝ)⁻¹)

lemma payload_jet (e) (h : PaidShadow W C Λ σ) (ht : 0<σ) (v : Dir G n) :
   tag e (payload W v p)= tag e (bench W v p) + ⨳ * ∑ s : Signed, ((∑ x, tag e (song (pulled v s) x W.cubic))+(∑ x,tag e (song (pulled v s) x W.quartic))) := by
  let t := pulled v
  let F s := (∑ x : Face (Per n), (ringLit (t s) p x + (1/2:ℝ) • words (t s) x.1 (fun i => score W x.2 i.1)))
  have hF (s:Signed) : ContDiff ℝ ∞ (F s) := flow_sum fun i=> ((lit_flow _ _ _).of_le le_top).add (ContDiff.const_smul (1/2:ℝ) (words_flow _ _ (paid_chord W h i.2) ht)) -- replace
  let G₁ s:=(∑ x:Site n, song (t s) x W.cubic)
  let G₂ s:=(∑ x:Site n, song (t s) x W.quartic)
  have hG₁ (s:Signed) : ContDiff ℝ ∞ (G₁ s) := flow_sum fun x=>song_smooth _ h.coeffThree ht x
  have hG₂ (s:Signed) : ContDiff ℝ ∞ (G₂ s) := flow_sum fun x=>song_smooth _ h.coeffFour ht x
  have hs' {f : ℝ→ℝ} (ht : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (⨳ • f) := by change ContDiff ℝ ∞ (fun x=> ⨳ • f x); exact ContDiff.const_smul ⨳ ht
  unfold payload bench; change tag e (⨳ • ∑ s, (F s + G₁ s + G₂ s)) = tag e (⨳ • ∑ s,F s) + _
  simp only [Finset.sum_add_distrib,smul_add]
  rw [tag_add (q:=e) (⨳ • (∑ x,F x) +⨳ • (∑ x, G₁ x)) (⨳ • (∑ x,G₂ x)) ((hs' (flow_sum hF)).add <| hs' (flow_sum hG₁)) (hs' (flow_sum hG₂)), tag_add _ _ (hs' (flow_sum hF)) (hs' (flow_sum hG₁)),add_assoc]; congr 1
  rw [tag_smul _ (flow_sum hG₁),tag_smul _ (flow_sum hG₂), tag_sum G₁ hG₁, tag_sum G₂ hG₂, ←mul_add]; congr 1; congr 1 <;>
    refine Finset.sum_congr rfl fun s _=> ?_
  · exact tag_sum _ fun x=> song_smooth _ h.coeffThree ht x
  exact tag_sum _ fun x=> song_smooth _ h.coeffFour ht x

lemma bench_jet (e) (h : PaidShadow W C Λ σ) (ht : 0<σ) (v : Dir G n) :
   tag e (bench W v p)= ⨳ * ∑ s : Signed, ∑ x : Face (Per n), (tag e (ringLit (pulled v s) p x) +(1/2:ℝ) * tag e (words (pulled v s) x.1 (fun i => score W x.2 i.1))) := by
  unfold bench
  have hF (s:Signed) (x : Face (Per n)) : ContDiff ℝ ∞ (ringLit (pulled v s) p x + (1/2:ℝ) • words (pulled v s) x.1 (fun i=>score W x.2 i.1)) :=
    ((lit_flow _ _ _).of_le le_top).add (ContDiff.const_smul (1/2:ℝ) (words_flow (G:=G) _ x.1 (W:=fun i=>score W x.2 i.1) (paid_chord W h _) ht))
  rw [tag_smul _ (flow_sum fun s=> flow_sum <| hF s), tag_sum _ (fun s=> flow_sum (hF s))]; refine congr_arg (⨳*·) (Finset.sum_congr rfl fun s _ =>?_)
  rw [tag_sum _ (hF s)]
  apply Finset.sum_congr rfl; intro i _; rw [tag_add _ _ ((lit_flow _ _ _).of_le le_top), tag_smul _ (words_flow _ _ (paid_chord _ h i.2) ht)]
  exact ContDiff.const_smul (1/2:ℝ) (words_flow _ _ (paid_chord _ h i.2) ht)

lemma qulit_smooth b (h : PaidShadow W C Λ σ) (ht : 0<σ) (v : Dir G n) : ContDiff ℝ ∞ (qulit W b v p) := by
  unfold qulit facet; exact ContDiff.const_smul ((Fintype.card Signed:ℝ)⁻¹) <| flow_sum fun s:Signed=> flow_sum fun x: Face (Per n)=> ((lit_flow _ _ _).of_le le_top).add <| ContDiff.const_smul (1/2:ℝ) (air_smooth _ _ _ (paid_chord _ h x.2) ht)
lemma qulit_jet (e b) (h : PaidShadow W C Λ σ) (ht : 0<σ) (v : Dir G n) :
   tag e (qulit W b v p)= ⨳ * ∑ s : Signed, ∑ x : Face (Per n), (tag e (ringLit (pulled v s) p x) + (1/2:ℝ)*tag e (liftAir (pulled v s) b x.1 (fun i=>score W x.2 i.1))) := by
  unfold qulit facet
  have hF (s:Signed) (x : Face (Per n)) : ContDiff ℝ ∞ (ringLit (pulled v s) p x + (1/2:ℝ) • liftAir (pulled v s) b x.1 (fun i=>score W x.2 i.1)) :=
    ((lit_flow _ _ _).of_le le_top).add (ContDiff.const_smul (1/2:ℝ) (air_smooth _ b _ (paid_chord _ h x.2) ht))
  rw [tag_smul _ (flow_sum fun s=>flow_sum (hF s)),tag_sum _ (fun s=>flow_sum (hF s))]; refine congr_arg (⨳*·) (Finset.sum_congr rfl fun s _=>?_)
  rw [tag_sum _ (hF s)]; apply Finset.sum_congr rfl; intro i _; rw [tag_add (q:=e) _ _ ((lit_flow p (pulled v s) i).of_le le_top) (show ContDiff ℝ ∞ ((1/2:ℝ) • liftAir (pulled v s) b i.1 (fun t=> score W i.2 t.1)) from ContDiff.const_smul (1/2:ℝ) (air_smooth (pulled v s) b i.1 (paid_chord _ h i.2) ht)),tag_smul _ (air_smooth _ b _ (paid_chord _ h i.2) ht)]


def riser (G : Gauge) := 192*curveBill G*(1+K G*G.colorScale)
def reel (G : Gauge) (q) (C σ Y D : ℝ) := 3^q*10*allowance q σ*(riser G)^q*(C+1)^2*(Fintype.card G.ColorIndex+3:ℝ)*gain D (D+Y) q
def baseCost (G : Gauge) (q) (σ : ℝ) (v : Dir G n) := 3^q*10*allowance q σ*(riser G)^q*gain ‖dColor G n 1 v‖ (‖dColor G n 1 v‖+ ‖v‖) q

def qulitGap (e) (v : Dir G n) (D : Shadow G) (p : Clip) := tag e (payload D v p)-tag e (qulit D false v p)
end YM.UVExt.Paths
