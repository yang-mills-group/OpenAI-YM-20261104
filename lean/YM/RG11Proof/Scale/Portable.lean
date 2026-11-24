import YM.RG11Proof.Scale.Limits

/-! # CS and engineering conversion require only the displayed truncated match -/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Scale
open scoped BigOperators Classical Topology
open PowerSeries YM.PertExtension.Position YM.RG11.Jets
variable {J P:Type*}[Fintype J]{width:P→ℕ}

def clip (N:ℕ)(c:Change ℝ J): Change ℝ J:= ⟨keep N c.g,c.Z.map (keep N)⟩
omit [Fintype J] in
@[simp] theorem clip_square (N:ℕ)(c:Change ℝ J)(k:ℕ): piece k (clip N c).Z= if k≤N then piece k c.Z else 0:=Matrix.ext fun i j=>by
   by_cases hi:k≤N <;> simp only [clip,piece_apply,Matrix.map_apply,keep,coeff_mk,hi,↓reduceIte,Matrix.zero_apply]

-- truncated extensions
omit [Fintype J] in
 theorem clip_agrees (N:ℕ)(c:Change ℝ J):Change.EquivJet (clip N c) c N:=
   ⟨keep_through _ _, MatThrough.of_piece fun i hi=>by rw [clip_square, if_pos hi]⟩

theorem clip_law (N:ℕ)(c:Change ℝ J){L:Constraints ℝ J}(h:L.Lawful c.Z):L.Lawful (clip N c).Z where
   baseline:=(clip_square N c 0).trans ((if_pos (Nat.zero_le ..)).trans h.baseline)
   positive {i} hi:=by rw [clip_square]; split <;> first |exact h.positive hi|exact L.vary.zero_mem

-- Only finite order premises on graded Z
 theorem graded_thru {L:Constraints ℝ J}(p:Change ℝ J)(hl:L.Lawful p.Z)(hp:Anchored p.g)
    {N}{w:J→ℕ}(h:∀ k≤N,graded w (piece k p.Z))(E:Keeper width){A B:ArrayAt J ℝ width}(hx:Sees L A)
    (he:∀ v,Through N (p.act A v) (B v))
    {β μ:PowerSeries ℝ}{b m:Square J (PowerSeries ℝ)}(ha:Stem N E w A μ m)(hb:Stem N E w B β b)
    (hβ:Anchored β)(hM:vertical (L:=L) m)(hB:vertical (L:=L) b):
   Through N (β*derivative ℝ p.g) (PowerSeries.subst p.g μ) ∧
     MatThrough N (β • (flash p.Z)) (b*p.Z - p.Z * subs p.g m):=by
   let q:= clip N p
   have hq:= clip_agrees N p
   change Change.EquivJet q p N at hq
   have hz : Anchored q.g:= hq.ruler.head.trans hp
   have hh := transports q (clip_law N p hl) hz (w:=w) (graded.piece_all.mpr (fun i=> by
      change graded w (piece i (clip N p).Z)
      rw [clip_square]; split
      · exact h i (by omega)
      · exact graded.zero)) E hx (fun i=> (hq.act (v:=i) hz (fun _=> Through.refl (A _))).trans (he i)) ha hb hβ hM hB
   have hr : Through N β β:=Through.refl _
   refine ⟨(through_weighted hq.ruler.symm hr hβ).trans (hh.1.trans ((Through.refl _).compose hq.ruler hz)),fun i j=>?_⟩
   have hi : Through N ((β • flash p.Z) i j) ((β • flash q.Z) i j):=through_weighted (hq.field i j).symm hr hβ
   exact hi.trans ((hh.2 i j).trans (((MatThrough.refl b).mul hq.field i j).sub (hq.field.mul ((MatThrough.refl m).subs hq.ruler hz) i j)))

/-- Physically frames may have been found under different finite rank
calibration equations, or not calibrated by this rank argument at all. At a
horizon h where a truncated equality on the reports has been ESTABLISHED,
exact engineering laws and CS on those SAME reports imply the change law and
graded coefficients through precisely that truncation. Independent of any
order n+1 report match and DOES NOT derive such a match. Price to use joint
detector includes a genuine order-one transverse response on A, incl if N=0.
Use `Fields/Scale` bindings for Yang--Mills instantiations. Uses free and sees
here separated only for convenience; provide Sees and derive Free. -/
theorem stamp_transport {L:Constraints ℝ J}(p:Change ℝ J)(hl:L.Lawful p.Z)(hp:Anchored p.g)
    {N}{w:J→ℕ}(hq:Permits J w L)(s:ℝ→Keeper width)(h₀:s 0=Keeper.id width)(E:Keeper width)
    {A B:ArrayAt J ℝ width}(hx:Sees L A)(hr:Free L A)(hgA:Engineering w s A N)(hgB:Engineering w s B N)
    (he:∀ v,Through N (p.act A v) (B v))
    {β μ:PowerSeries ℝ}{b m:Square J (PowerSeries ℝ)}(ha:Stem N E w A μ m)(hb:Stem N E w B β b)
    (hβ:Anchored β)(hM:vertical (L:=L) m)(hB:vertical (L:=L) b):
   (∀ k≤N,graded w (piece k p.Z)) ∧ Through N (β*derivative ℝ p.g) (PowerSeries.subst p.g μ) ∧
     MatThrough N (β • (flash p.Z)) (b*p.Z - p.Z * subs p.g m):=by
   have h:=match_stamp hq hl hp hgA hgB h₀ he hr
   exact ⟨h,graded_thru p hl hp h E hx he ha hb hβ hM hB⟩
end YM.RG11.Scale
