import YM.OPE.Compatible.Ingle.Tape
/-!
# Receipt ledger for stencil costs. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Spells
open Function Filter Set Lattice Wilson RG MeasureTheory Matrix
open Pill Asymptotics Flume Flume.Page Flume.Script
open Next.Free Bloch FreeResolvent Cascade Score Terp KernelChoices Paver Silt.Float Source Silt Jargon -- inspect
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I X Y:Type}{β β' p x g y:I→ℝ}{f:Filter I}{s:ℝ}{G:Gauge}
variable {U:I→BudgetPoint} {v:I→Side}  -- r undeclared
variable {r k m:ℕ}{b:I→ℕ}
-- capacity
variable (h:Tendsto β f atTop)
include h
lemma CashB (hp:Receipt β f (fun i=>(b i:ℝ))): Receipt β f (fun i=>sizeQ (b i)):=by
       let J:= carth h; have hx:=hp.plus hp J; let hc:= Score.steady (1:ℝ) J; refine (hc.plus (((hx.plus hc J).power 4 J).product (Score.steady (4:ℝ) J)) J).pointwise (Eventually.of_forall fun i=> ?_) (Eventually.of_forall fun i=> add_nonneg zero_le_one (Nat.cast_nonneg _)); exact scoopμ (b i) ⟨2*(b i+1)+1,by omega⟩ 0 (lt_add_one _)
lemma cashS (G:Gauge)(hp:Receipt β f (fun i=>(b i:ℝ))):Receipt β f (fun i=>(Fintype.card (Fpaper G (b i)):ℝ)):=by
       simp_rw [Fpaper,Fintype.card_prod,Nat.cast_mul]; apply Score.product _ (Score.steady _ (carth h)); exact (CashB h hp).pointwise (Eventually.of_forall fun i=>le_add_of_nonneg_left zero_le_one) (Eventually.of_forall fun i=>Nat.cast_nonneg _)
lemma cashRoster (j:ℕ)(hp:Receipt β f (fun i=>(b i:ℝ))): Receipt β f (fun i=>((j*b i:ℕ):ℝ)):=by push_cast; exact (Score.steady _ (carth h)).product hp
open MSbar.Tree MSbar.Tree.Resolvent Streamer
lemma costK (G:Gauge)(A:KernelChoices)(u:I→Train r)(hs:4 ≤ r) (hp:Receipt β f (fun i=>(b i:ℝ))): Receipt β f (fun i=> cookV G (u i) A hs (v i) (b i)):=by
       let TQ (ρ:ℝ):=Score.steady ρ (carth h); let H:= carth h; apply Score.product ((TQ _).product ((cashS h G (cashRoster h 4 hp)).power 2 H)); exact Score.power _ ((TQ _).product (((TQ _).plus ((TQ _).product hp) H).product (TQ _))) H
lemma nubby (G:Gauge)(A:KernelChoices)(u:I→Train r)(hs:4 ≤ r) (hp:Receipt β f (fun i=>(b i:ℝ))): Receipt β f (fun i=> nubK G (b i) (u i) A hs (v i)):= (Score.steady _ (carth h)).plus (((cashS h G hp).product (Score.steady _ (carth h))).product (costK h G A u hs hp)) (carth h)
-- ray triangle
lemma ηlease (j:ℕ)(A:ℂ→L[ℝ]ℝ) (P:Pad G)(hg:Receipt β f x)(hp:Receipt β f (fun i=>(b i:ℝ))) : Receipt β f (fun i=> θW P (b i) j (x i) A) :=by
       apply Score.product _ (Score.steady _ (carth h)); exact (((Score.steady _ (carth h)).product ((CashB h hp).power j (carth h))).product hg)
omit h
lemma Stripρ (ht:TuneUp β f U p)(P:Pad G)(A:ℂ→L[ℝ]ℝ)(k:ℕ)(b:I→ℕ)(c: I→ℝ)(w:I→ℝ)(hq:Receipt β f w)(hx:Receipt β f c)(hp:Receipt β f y) (hv:Receipt β f (fun i=>(b i:ℝ))): Wickρ β f (fun i=> priceArc (w i) P A k (b i) (y i) (U i) (p i) (c i)):=by
       have h:= ht.Clock; intro a; let f:(B:OrderedFinpartition k)→ I→ℝ:=fun B i=> θW P (b i) B.length (y i) A * B.length*w i^(B.length-1)*w i*(U i).threshold+θW P (b i) (B.length+1) (y i) A * θh (p i) (U i) * w i^B.length * c i; apply RateLE.sum (S:=Finset.univ) (f:=f) (carth (carth h)); intro B _; apply RateLE.add _ _ (carth (carth h)); · exact Wickρ.dot ((((ηlease h B.length A P hp hv).product (Score.steady _ (carth h))).product (hq.power _ (carth h))).product hq) (lagG ht) a
       refine (Wickρ.dot (((ηlease h (B.length+1) A P hp hv).product (hq.power B.length (carth h))).product hx) (πlag ht) a).congr (Eventually.of_forall fun i=>?_); ring
lemma tankρ (ht:TuneUp β f U p)(P:Pad G)(A:ℂ→L[ℝ]ℝ)(d:ℕ)(b:I→ℕ)(c: I→ℝ)(w:Fin (d+1)→I→ℝ)(hq:∀ i,Receipt β f (w i))(hx:Receipt β f c)(hp:Receipt β f y) (hv:Receipt β f (fun i=>(b i:ℝ))): Wickρ β f (fun i=> PolyRayX (fun j=>w j i) P A (b i) (y i) (c i) (U i) (p i)):=by
       intro a; exact RateLE.sum (carth (carth ht.Clock)) (fun (i: Fin (d+1)) _=> Wickρ.dot (Score.steady _ (carth ht.Clock)) (Stripρ ht P A i.val b c (w i) (hq i) hx hp hv) a)
end YM.OPE.Spells
