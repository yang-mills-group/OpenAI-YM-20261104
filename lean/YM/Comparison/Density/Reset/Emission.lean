import YM.Comparison.Density.Reset.Dials

/-!
Actual flagged Mask closures after an uncertain scalar & affine
readjustment, charged from SAME poly data. Scalar computed per site
(nonextensive difference). AGAIN, `newRep.beta` is temporary.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.Density.Reset
open Fusing Markers Testing Registers Marker RG Lattice Function Finset MeasureTheory Filter Wilson
open Pert.Attach Push.AbsoluteSums Assembly Ovens Extra.Iteration
open Progress.DirectedRecipe AnalyticBridge.VerifiedReset AnalyticBridge.VerifiedReset.Collection
open WilsonStartup Averaging Geo UVNext.CouplingReset
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {n : Side} {G : Gauge}

variable (V : Type) [DecidableEq V] (R : Census V) (X : V → Type) [∀ v,NormedAddCommGroup (X v)] [∀ v,NormedSpace ℂ (X v)]
variable (P : Rep G n) (A M : Activities G n)

def spill : Leftovers R X G n:= ⟨⟨(dip A P).softer,(trade A P).logarithm⟩,fun _ _ _=>0⟩
def newRep := boundAlong P (exitPath A P M) (spill V R X P A)

variable {V R X P A M} {e b a c σ C Λ : ℝ} {O : Readers V X n} {w : V→ℝ} {Q : Assembly R X G n}
namespace Panel
variable (g : G.Simple) (h : Panel M A P e b a c σ C Λ)
include g h
lemma lot : Placed P.p O (spill V R X P A) := by
  let X:=dip A P; let L:=trade A P; let F:= X.softer
  have he:= h.ramp g
  refine ⟨X.sites,⟨fun i U hh=> ?_,he.steady,he.reads,he.looks,fun s b=>?_⟩,fun x=> ?_,fun _ _ _=>rfl,fun _ _ _ _=>rfl,fun _ _=>Catalogue.empty⟩
  · by_contra H; exact he.visits i U H hh
  · obtain ⟨u,hu,hv⟩:=he.carries s b; exact ⟨u,hu,fun i U=>hv U i⟩
  exact ⟨fun _ _ _=>rfl,fun _=>measurable_const,fun _ _ _ _ _=>rfl,fun _ _=> carry_zero⟩
omit [∀ v, NormedSpace ℂ (X v)] in
lemma streamed : Compensated P.p O (spill V R X P A) w (e+1) (softNeed G (later P.p e h.growth) P.clip σ C 0 a) := by
  have hh:=h.travels; obtain ⟨u,hu,hb⟩:=hh.cheap
  let B:=later P.p e h.growth
  obtain ⟨-,he⟩:=Local.quote_family h.angles h.safe h.width 0 _ hu hb (delta_bound g hh.projects)
  have hk : Over (0:Poly R) 0 := by simpa using (over_unit (R:=R)).scale (s:=0) (t:=0) (by simp)
  refine ⟨_,fun _=>0,fun i U=> Local.quote_soft (R:=P.path) (c:=P.clip) g 0 _ hu hh.smooth (numbering _ i) U,fun _=>carry_zero,fun _=>rfl,fun _ _ _ _=>hk,fun x=>?_⟩
  simpa only [Poly.zero_price,add_zero,← add_assoc] using! Cost.equiv (numbering _) (he x)
omit [∀ v, NormedSpace ℂ (X v)] [∀ v,NormedAddCommGroup (X v)] in
lemma rebates : Conversion P Q (exitPath A P M) Q.exponent (spill V R X P A):=
    ⟨rfl,h.reset_terms g,fun x U=>by unfold spill; dsimp only; rw [tsum_zero,add_zero]⟩
omit [∀ v, NormedSpace ℂ (X v)] [∀ v,NormedAddCommGroup (X v)] in
lemma reflected : (newRep V R X P A M).activities.RegularFamily P.p := by
  have hr:= weave_family h.model (h.regular g); exact ⟨hr.smooth,hr.at_flat,hr.vanish⟩
lemma exitMoves (s x) : Nonempty ((exitPath A P M).activities.Moves s x) :=
    ⟨weave_moves ((h.modelMoves s x).some) (((h.ramp g).moves s x).some)⟩
end Panel
variable [Fintype V]

def output (P : Rep G n) (Q : Assembly R X G n) (A : Activities G n):= restored P Q Q.exponent (spill V R X P A)

theorem vacancies (hw : ∀ i,0<w i) (g : G.Simple) (h : Panel M A P e b a c σ C Λ)
    {Y Z bP q m κ : ℝ} (hd : Assembly.Tidy P w O Q Y Z (e+1) bP)
    (hp : let r:=softNeed G (later P.p e h.growth) P.clip σ C 0 a; q*bP+r*Real.exp r ≤ m)
    (hq : 1 ≤ q) (hm : 0 ≤ m) (hz : ((P.p.B+P.p.B+1:ℕ):ℝ)^4*m ≤ 1) (hk : 0 < κ):
    let T:= newRep V R X P A M
    let F:= output P Q A
    let N:=net A P
    let S:=later P.p e h.growth
    let W:=(Real.exp m-1)/q
    let E:=regularNeed G S P.clip σ C 0 a
    T.p=P.p ∧ T.path=P.path ∧ T.clip=P.clip ∧ T.v=P.v-(∑' i, A.E i 1)/UVNext.CouplingReset.sites n ∧ |T.v-P.v|≤a ∧
    T.beta=P.beta+delta A ∧ |delta A|≤a/P.p.threshold^2 ∧
    T.eval=P.eval ∧ (∀ x,F.eval T x= Q.eval P x) ∧
    T.activities.reg=(weave M N).reg ∧ T.activities.E=(weave M N).E ∧
    T.activities.RegularFamily P.p ∧ T.activities.EBound S (c+E) ∧
    N.RegularFamily P.p ∧ N.EBound S E ∧
    F.exponent=Q.exponent ∧ F.Tidy T w O Y Z e W ∧
    T.activities.ForcedFamily T.p ∧ T.activities.KBound S W ∧
      (∀ s x, Nonempty (T.activities.Moves s x)) ∧ Account S w O.source (ranges T.activities) F.arms κ (W/κ) := by
  intro T F N S W E
  have he:=Fusing.extent (Z:=exitPath A P M) hw h.growth hd (h.lot g) (h.streamed g) hq hm hz hp h.forces rfl hd.layout hd.growth
  have hi x : F.eval T x= Q.eval P x:=funext fun U=> enact hw h.growth hd (h.lot g) (h.streamed g) _ _ (h.rebates g)
  refine ⟨rfl,rfl,rfl,rfl,h.scalar g,rfl,(le_div_iff₀ (sq_pos_of_pos P.p.threshold_pos)).mpr ((mul_comm ..).trans_le (h.projection g)),?_,hi,rfl,rfl,h.reflected g,
    weave_bound h.lesser (h.listed g),h.regular g,h.listed g,rfl, he,Fusing.progress (Z:=exitPath A P M) hw h.growth hd (h.lot g) (h.streamed g) hq hm hz hp h.forces rfl hd.layout hd.growth h.rotates (h.exitMoves g) hk⟩
  change Assembly.Tidy T w O F Y Z e W at he
  funext U; apply Complex.ofReal_injective
  rw [← Assembly.zero_order hw h.growth he 0, hi 0, Assembly.zero_order hw (by linarith [h.growth]) hd]
end YM.Comparison.Density.Reset
