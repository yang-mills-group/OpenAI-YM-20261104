import YM.MSbar.Pole.Feynman.Exhale

/-! # Polchinski at d=4 by removing dimensional regulator -/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole.Feynman.Menu
open Function Set Filter MeasureTheory Ambient Momentum Age Mellin Piece Sew Thread Symbol PoleVal District
open scoped Topology ContDiff BigOperators Classical Interval Real
variable {I V : Type} [Fintype I] [Nonempty I]

-- scale integrand in the actual dimensional prescription in compact positive intervals
variable {μ r : ℝ}
def line (C : Menu I V) (μ r:ℝ) (D:District I V) (e : I×I) : ℂ→Cloud I :=
    let E:= D.less e; let T:=D.thread C.chart e
    let L:=within (C.pick D e) e D C.chart; let R:=within (D.lands\C.pick D e) e D C.chart
    if E.Crossing C.chart then Integrates μ (T.spun r (C.primitive μ E r)) else
       T.twig (minus L C.chart e) r (C.primitive μ L r * C.primitive μ R r)
variable {C : Menu I V} {D:District I V} {e:I×I}
variable (h:D.Clear C.chart) (hv:e ∈ D.paths)(hμ:0<μ) (hr:0<r)

include h hv
private lemma clear_gap (hs : ¬(D.less e).Crossing C.chart) :
    Gap (C.pick D e) e D C.chart := by -- include
  rw [pick,dif_pos (h.splits hv hs)]; exact Classical.choose_spec (h.splits hv hs)
local notation "X" => within (C.pick D e) e D C.chart
local notation "Y" => within (D.lands\C.pick D e) e D C.chart
local notation "T" => D.thread C.chart e
include h hv hμ hr
private lemma coalesce (hp:Gap (C.pick D e) e D C.chart) :
    let J:= X; let K:=Y; let c:=C.chart; let t:= T
    Stack (mix (C.run μ J).body (C.run μ K).body) c.mom (J.weight c+K.weight c) (t.inputs∪(t.chain.reads∪D.opens c)) (t.chain.reads∪D.opens c):= by
  intro J K c t
  have hg := h.content hv hp; have hJ:= done C μ hg.1 hμ; have hK:= done C μ hg.2 hμ
  have ha:Disjoint (J.opens c) (K.opens c):= c.hands_separate (District.borders J c) (District.borders K c) (h.split_disjoint hv hp)
  have hd₁ : Disjoint (J.opens c) (K.view c):= Finset.disjoint_union_right.mpr ⟨hg.1.notations.symm.mono_right ((Finset.erase_subset _ _).trans (District.borders K c)),ha⟩
  have hd₂ : Disjoint (K.opens c) (J.view c):= Finset.disjoint_union_right.mpr ⟨hg.2.notations.symm.mono_right ((Finset.erase_subset _ _).trans (District.borders J c)),ha.symm⟩
  have hk:= smash hJ hK hd₁ hd₂
  apply Stack.raises hk
  · rw [show t.inputs=J.mouths c∪ K.mouths c from (h.sameMark hv).trans (h.split_union hv hp).symm, show t.chain.reads∪D.opens c=J.opens c∪K.opens c from (h.corresponds hv).trans (h.split_chart hv hp).symm]
    change J.view c ∪ K.view c ⊆ _; intro i hx; simp only [District.view,Finset.mem_union,Finset.mem_erase] at *; tauto
  exact ((h.corresponds hv).trans (h.split_chart hv hp).symm).le

lemma movesUp :
    let A:= C.glimpse μ D (C.run μ) e
    C.line μ r D e =ᶠ[approaching] Piece.sum A C.chart.mom (D.weight C.chart) r ∧
    Young C.chart D A:=by
  intro A; let t:= D.thread C.chart e; let K:= D.less e
  have ht:=h.sameMark hv; have hK:=h.unmoored hv; have hh:=h.permission hv
  have hp:t.inputs ⊆ C.chart.mom:= ht.symm ▸ K.borders C.chart
  by_cases H:K.Crossing C.chart
  · have hs: K.Clear C.chart:= h.pauses hv H; let U:=(C.run μ K).body; have hu:=done C μ hs hμ
    have he: A = U.map (leap t μ):= by dsimp only [A,glimpse]; rw [if_pos H]
    have h₁ : Stack U C.chart.mom (K.weight C.chart) (t.inputs ∪ (t.chain.reads∪D.opens C.chart)) (t.chain.reads∪D.opens C.chart) := by
      rw [show t.inputs=_ from ht,show t.chain.reads∪D.opens C.chart=_ from h.corresponds hv]; apply Stack.raises hu _ (by rfl); exact Finset.union_subset_union (Finset.erase_subset _ _) (by rfl)
    rw [he]; refine ⟨?_, District.herald h hv hu hμ⟩; dsimp only [line]; rw [if_pos H,h.counting hv]; exact self_flow hh hp hK h₁.graded hr μ
  have hm : Gap (C.pick D e) e D C.chart:= clear_gap h hv H
  have hy:= h.content hv hm
  let J:= X; let S:= Y; let U:= (C.run μ J).body; let V:=(C.run μ S).body
  let Q:=mix U V; let R:= minus J C.chart e
  have hl:R ⊆ t.output:= h.alignment hv hm
  rw [show A= Q.map (ramp t R) by dsimp only [A,glimpse]; rw [if_neg H]; rfl]
  refine ⟨?_,District.across h hv hm (done C μ hy.1 hμ) (done C μ hy.2 hμ)⟩; dsimp only [line]
  rw [if_neg H];
  change t.twig R r (Piece.sum U _ _ _ * Piece.sum V _ _ _) =ᶠ[approaching] _; rw [← combined C.chart.mom]
  · rw [show D.weight C.chart= J.weight C.chart+S.weight C.chart+2- (t.chain.demand:ℤ) by rw [h.counting hv,show J.weight C.chart+S.weight C.chart=_ from h.split_count hv hm]; change _= _+_-(t.chain.demand:ℤ); ring]
    exact Piece.bridge hh hp hK (coalesce h hv hμ hr hm).graded hr R hl
  exact hr

/-- Exact projected rhs, no positive-order regulator left in this formula for one RG differentiation
(except the soft/IR proper time). -/
def joins (C : Menu I V) (μ r:ℝ)(D:District I V) (e:I×I)(x : External I 2):=
    let E:= D.less e; let T':= D.thread C.chart e
    if E.Crossing C.chart then
      ((π:ℂ)^2)⁻¹*(∫ t:place 2,T'.spun r (fun _=> C.connected μ E r) 0 2 (t,x))*factor μ 0
    else
      let L:=within (C.pick D e) e D C.chart; let R:=within (D.lands\C.pick D e) e D C.chart
      T'.twig (minus L C.chart e) r (fun _=> C.connected μ L r*C.connected μ R r) 0 2 x
lemma collapse (x : External I 2):
    let K:= sum (C.glimpse μ D (C.run μ) e) C.chart.mom (D.weight C.chart) r
    PoleVal.pay K 2 x=C.joins μ r D e x:= by
  intro K; obtain ⟨hh,hk⟩:=movesUp h hv hμ hr
  have he := Piece.Flag.clean hk _ hr
  rw [show PoleVal.pay K=_ from (PoleVal.eq he hh.symm).symm]; dsimp only [joins,line]; split_ifs with ht
  · let W:=C.chart; have hh := h.pauses hv ht; refine exhale (h.permission hv) hr (rolls hμ hr hh) ?_ x hμ
    have hs:= Stack.raises (done C μ hh hμ) (show (D.less e).view W⊆ (D.thread W e).inputs ∪ ((D.thread W e).chain.reads∪D.opens W) by
      rw [show (D.thread W e).inputs=_ from h.sameMark hv,show (D.thread W e).chain.reads∪D.opens W=_ from h.corresponds hv]; exact Finset.union_subset_union (Finset.erase_subset _ _) (by rfl)) ((h.corresponds hv).le)
    exact senses (fun p hp=> (hs.graded p hp).shape) (h.unmoored hv) (District.weight ..) r
  have hz := h.content hv (clear_gap h hv ht); have hs:=rolls hμ hr hz.1; have hp:=rolls hμ hr hz.2
  rw [walking (hs.mul hp),PoleVal.product hs hp]; rfl
omit hv in
theorem inFour (x : External I 2)(hp:D.paths.Nonempty) :
    HasDerivAt (fun s => C.connected μ D s 2 x) ((r:ℂ)⁻¹*((D.paths.toList.map (fun i => joins C μ r D i x)).sum)) r := by
  apply (block h hμ hr 2 x hp).congr_deriv
  let g i:=C.glimpse μ D (C.run μ) i; let K (L:List (I×I)):= sum (L.flatMap g) C.chart.mom (D.weight C.chart) r
  have he (L : List (I × I)) (hl : ∀ p∈L,p∈ D.paths): Vortex 0 (K L) ∧ PoleVal.pay (K L) 2 x=(L.map fun i=>joins C μ r D i x).sum := by
    induction L with
    | nil=> exact ⟨Vortex.zero _,by rw [show PoleVal.pay (K [])=0 from PoleVal.paid (fun _ _=> tendsto_const_nhds)]; simp⟩
    | cons i L ih=>
      obtain ⟨hg,ht⟩:= ih (fun p hp => hl p (List.mem_cons_of_mem _ hp)); have hi:=hl i List.mem_cons_self
      have hy:= Piece.Flag.clean (movesUp h hi hμ hr).2 r hr
      rw [show K (i::L)= _+ K L from sum_cat ..]; refine ⟨hy.add hg,?_⟩; rw [sumValues hy hg]; exact congr_arg₂ (·+·) (collapse h hi hμ hr x) ht
  exact congr_arg _ (he D.paths.toList (fun _ i=>Finset.mem_toList.mp i)).2
end YM.MSbar.Pole.Feynman.Menu
