import YM.WilsonCoeffUV.Reclosure.TaylorLift
/-!
# Projection onto curvature alphabet, crossing rank in both directions

Ordered per grade for extraction; *actual analytic packet on tori through all orders*,
bulk jets don't discard ambiguity; uniqueness asked only on full standard projections.
Consumer uses `Display` for a choice of prescribed paths (can extend any paid
previous choices). Difference budgets correlate choices only by using extra entries.
This is not activity norm transportation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank.Mosaic
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power Stationary AnalyticNext.QuarticMatch.Estimate Near PowerSeries
open scoped ContDiff Topology BigOperators
variable {G:Gauge}{c:Side}{N M e m i k r t:ℕ}{s S a b u v:ℝ}{W X F:Canvas G}

-- ledger rows. grade/rank. flexible order.
structure PrismA (G:Gauge) where
    grade:ℕ
    rise:ℕ
    rankA: rise≤ grade
    cells : Stack G rise
abbrev SeriesA (G:Gauge):= List (PrismA G)

def recordV (P:PrismA G) : Canvas G:= chess P.cells P.grade
lemma presenceV (P:PrismA G)(p:e<P.grade): recordV P e=0:= if_neg (by omega)
lemma nimbus (P:PrismA G): recordV P P.grade (P.rise+2)=fire P.cells 0 (P.rise+2):=by rw [recordV,chess,if_pos le_rfl,Nat.sub_self]
lemma zero_lane (P:PrismA G)(p:¬ e < P.grade → P.rise+2+(e-P.grade)≠ r) : recordV P e r=0:=by
    by_cases h:e<P.grade; rw [presenceV P h]; rfl
    rw [recordV,chess,if_pos (by omega)]; exact shine_dark (p h)

def murals (X:SeriesA G): Canvas G:= (X.map recordV).sum
lemma murals_nil : murals ([]:SeriesA G)=0:= rfl
lemma murals_cons (P:PrismA G)(X:SeriesA G) : murals (P::X)=recordV P+murals X:=rfl
lemma murals_append (X Y:SeriesA G): murals (X++Y)=murals X+murals Y:= by unfold murals; rw [List.map_append,List.sum_append]
def Draw (V:SeriesA G) (σ A:ℝ) : Prop:= 0≤ A ∧ ∀ i∈V, Commission i.cells σ A i.grade
lemma draw_nil (h:0≤ a): Draw ([]:SeriesA G) s a:=⟨h,by simp⟩
lemma Draw.light {P:SeriesA G}(h:Draw P s a)(p:S≤ s)(e:a≤ b): Draw P S b:=⟨h.1.trans e,fun i z=>(h.2 i z).change p e⟩
lemma Draw.both {P Q: SeriesA G}(h:Draw P s a)(e:Draw Q s a): Draw (P ++ Q) s a:= ⟨h.1,fun _ u=> (List.mem_append.mp u).elim (h.2 _) (e.2 _)⟩
-- Horizontal; include SIGN only when required (rank2); symmetry of composite already supplied for actual aggregation.

structure PointV (F:Canvas G)(e:ℕ) : Prop where
  ft : pillar F e
  symr : Pure (F e)
  hike r: stroll (F e r)
  hill r: Bank.mural (F e r)
  nilV r (p:r≤1 ∨ e+2 < r): F e r=0

structure Desc (F:Canvas G)(e:ℕ) (s A:ℝ) : Prop extends PointV F e where
  beats r: Amber terrain s A (F e r)
  sign : Spin (F e 2)
  aft : 0<e → Aware (F e 2)

lemma pillar_sub (h:pillar F e)(p:pillar X e): pillar (F-X) e:=by
   intro b x; unfold pillar at h p; specialize h b x; specialize p b x
   refine Eq.trans ?_ (show (∑ v:Axis, ∑ j:G.ColorIndex,∑ z∈Finset.antidiagonal e,(wickLamp b 0 (x,v) j z.1 (F z.2) + wickLamp 0 b (x-step v,v) j z.1 (F z.2)))-(∑ v:Axis,∑ j:G.ColorIndex,∑ z∈Finset.antidiagonal e,(wickLamp b 0 (x,v) j z.1 (X z.2)+wickLamp 0 b (x-step v,v) j z.1 (X z.2)))=0 by rw [h,p]; simp)
   simp_rw [Pi.sub_apply,floatT,← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro v _; apply Finset.sum_congr rfl; intro b _; apply Finset.sum_congr rfl; intro k _; abel
lemma tick_none (x y:G.Color)(i:Edge Cover)(j:G.ColorIndex)(k:ℕ): wickLamp (X:=ℝ) x y i j k 0=0:=by simpa using floatT (V:=ℝ) (0:Gen ℝ (YForest G)) x y i k j 0
lemma pillar0 (G:Gauge)(e:ℕ): pillar (0:Canvas G) e := by intro b x; simp [tick_none]
lemma pillar_sum (h:pillar F e)(p:pillar X e): pillar (F+X) e:=by
   have he:= pillar_sub (pillar0 G e) p; rw [zero_sub] at he; have hz:= pillar_sub h he; simpa only [sub_neg_eq_add] using hz
lemma mural_void (G:Gauge) (r:ℕ): Bank.mural (0:Ten ℝ (YForest G) r):= by intro u v x; simp
lemma PointV.zero (G:Gauge) (e:ℕ): PointV (0:Canvas G) e:= ⟨pillar0 G e,Pure.zero,fun _ _ _=>rfl,mural_void G,fun _ _=>rfl⟩
lemma PointV.sub (h:PointV F e)(p:PointV X e): PointV (F-X) e:=by
   refine ⟨pillar_sub h.ft p.ft,h.symr.sub p.symr,?_,?_,fun r b=> by simp only [Pi.sub_apply,h.nilV r b,p.nilV r b,sub_zero]⟩
   · intro r b x; simp only [Pi.sub_apply,h.hike r b x,p.hike r b x]
   intro r u v x; simp only [Pi.sub_apply,smul_sub,Finset.sum_sub_distrib]; rw [h.hill r u v x,p.hill r u v x]
lemma PointV.add (h:PointV F e)(p:PointV X e): PointV (F+X) e:=by
   have he:=(PointV.zero G e).sub p; rw [zero_sub] at he; simpa only [sub_neg_eq_add] using h.sub he
lemma axis (P:PrismA G)(h:0<s)(p:Commission P.cells s a P.grade)(e:ℕ): PointV (recordV P) e:=by
    have he x c:= postponed h p.toll (by omega) p.hue P.grade x c e
    have ht r (h:r≤1 ∨ e+2<r): recordV P e r=0:= zero_lane P (fun _=>by have hb:=P.rankA; omega)
    refine ⟨he,?_,?_,?_,ht⟩
    · unfold recordV chess; split; next h=> exact proven (by assumption) p.toll (by omega) _
      exact Pure.zero
    · intro r; unfold recordV chess; split; next he=> exact (paid_packet h p.toll (by omega) _ r).road
      exact fun b x=>rfl
    intro r; unfold recordV chess; split; next he=> exact dressing h p.toll (by omega) p.hue _ _
    exact mural_void G r
lemma soul {P:SeriesA G}(h:0<s)(p:Draw P s a)(e:ℕ): PointV (murals P) e:= by
   induction P with
   | nil=> exact PointV.zero G e
   | cons i P ih=> exact (axis i h (p.2 i (List.mem_cons_self ..)) e).add (ih ⟨p.1,fun _ x=>p.2 _ (List.mem_cons_of_mem i x)⟩)

def tax (G:Gauge)(s:ℝ)(e:ℕ) := ∑ k∈Finset.range (e+1),∑ i∈Finset.range (e+3), garden G s (k+2) i
lemma tax_nn (G:Gauge)(h:0<s)(e:ℕ): 0≤ Mosaic.tax G s e:= Finset.sum_nonneg fun _ _=>Finset.sum_nonneg fun _ _=>garden_nn G h _ _
lemma pollen (P:PrismA G)(h:Commission P.cells s a P.grade)(p:0<s)(e r:ℕ): Amber terrain (steep s) (a*Mosaic.tax G s e) (recordV P e r):=by
   have hp:=h.toll; have hz:=mul_nonneg (cap_nn hp) (tax_nn G p e)
   by_cases H:P.grade≤ e; swap; · unfold recordV chess; rw [if_neg H]; exact Amber.zero.le hz
   by_cases he:r≤ e+2; swap; · rw [(axis P p h e).nilV r (by omega)]; exact Amber.zero.le hz
   have ht := P.rankA
   have hZ:garden G s (P.rise+2) r≤Mosaic.tax G s e:= le_trans (Finset.single_le_sum (s:=Finset.range (e+3)) (f:=fun i=>garden G s (P.rise+2) i) (fun i _=>garden_nn G p _ _) (Finset.mem_range.mpr (by omega))) (Finset.single_le_sum (f:=fun k=>∑ i∈Finset.range (e+3), garden G s (k+2) i) (fun i _=>Finset.sum_nonneg fun _ _=>garden_nn G p _ _) (Finset.mem_range.mpr (by omega)))
   unfold recordV chess; rw [if_pos H]; exact (cap_pay p hp (by omega) _ _).le (mul_le_mul_of_nonneg_left hZ (cap_nn hp))
lemma pollen_sum {P:SeriesA G}(p:0<s)(h:Draw P s a)(e r:ℕ): Amber terrain (steep s) (P.length*(a*Mosaic.tax G s e)) (murals P e r):=by
   induction P with
   | nil=> simp; exact Amber.zero
   | cons i X ih=>
      have he:= ((pollen i (h.2 i (List.mem_cons_self ..)) p e r).add (ih ⟨h.1,fun j u=>h.2 j (List.mem_cons_of_mem _ u)⟩))
      apply he.le; simp [add_mul]; exact le_of_eq (add_comm ..)

def fromBefore (P:SeriesA G)(e:ℕ):= ∀ i∈P,i.grade<e
lemma empty_two {P:SeriesA G}(h:fromBefore P e): murals P e 2=0:=by
   induction P with
   | nil=> rfl
   | cons i X ih=> have hp:=h i (List.mem_cons_self ..); simp_rw [murals_cons,Pi.add_apply,zero_lane i (r:=2) (e:=e) (by omega),ih (fun j p=>h _ (List.mem_cons_of_mem _ p)),add_zero]
lemma fromBoth (P Q:SeriesA G)(h:fromBefore P e)(w:fromBefore Q e):fromBefore (P++Q) e:= fun i hi=> (List.mem_append.mp hi).elim (h i) (w i)

-- interval transversality without padding.
lemma tick_pillar (h:PointV F e) (t:∀ k<e,F k=0) (x:Cover)(c:G.ColorIndex) (r): windsL x c (F e (r+1))=0:=by
    let b : G.Color:= coatC G (Pi.single c 1)
    have H j (p:j∈ Finset.antidiagonal e) (hp:j≠ (0,e)): F j.2=0:=by have he:= Finset.mem_antidiagonal.mp p; apply t j.2; by_contra hh; exact hp (Prod.ext (show j.1=0 by omega) (show j.2=e by omega))
    let Z:= northL 0 x b (F e)
    have he: Z=0:= by
       rw [← h.ft b x]; unfold Z northL; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; rw [Finset.sum_eq_single_of_mem (0,e)]; exact Finset.mem_antidiagonal.mpr (by simp)
       intro k hk hp; rw [H k hk hp,tick_none,tick_none,add_zero]
    have hh:= wick_winds x c (F e) h.symr r; rw [show northL 0 x b (F e)=Z from rfl,he, ← Nat.cast_smul_eq_nsmul (R:=ℝ)] at hh
    exact (smul_eq_zero.mp hh.symm).resolve_left (by positivity)
end YM.WilsonCoeffUV.Bank.Mosaic
