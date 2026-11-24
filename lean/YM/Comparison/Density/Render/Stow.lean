import YM.Comparison.Density.Render.Goods
import YM.Comparison.Density.Budgets.Load

/-!
Rank-two exact full MASK re-expression uses marker-compatible actual
K identity. No assumed agreement on masked sector. Feed sign via exponent,
including a negative fork when subtracting this model entry (via a<0). This
can also be applied in encoding the formal model appending to represented
raw subtractions; any change of their masks afterwards needs the corresponding
exact alignment. Funding at exponent δ+3 from actual step exponents/ranks,
still needs numerical scenery rates as usual. Partner cost includes every
winding path.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.Density.Render.Frame
open Fusing Markers RG Lattice Function Finset MeasureTheory Filter Wilson
open Ovens Extra.Iteration Push.AbsoluteSums Marker
open Progress.DirectedRecipe AnalyticBridge.VerifiedReset AnalyticBridge.VerifiedReset.Collection
open WilsonStartup Averaging Geo Next.Scheduling Next.Scheduling.Wages Precision Work.F03 Work.G07 StressFlux
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical ContDiff InnerProductSpace
open Transport AnalyticBridge.SectorAffine.Offset FreeResolvent.Affine FreeResolvent.TestD
variable {G : Gauge} {n : Side} {B : BudgetPoint}

variable (F : ℕ→Atom G 2) (p : ℕ → Prop) (B : BudgetPoint) (n : Side) (a : ℝ)

abbrev full : ℕ→Prop:= fun _=>True

def pollenMark (i : ℕ) := masked B.threshold (halo 2 {(0:Site n)}) (recipe a full i • pollen (0:Site n) (F i))

-- Measures on corresponding sectors, SAME support spanning each
-- tested earlier footprint. Before reading +/- prefactors.
protected def deficit (i : ℕ) := masked B.threshold (rosebud F n i) ((makeRose F n a full).dataF i)+pollenMark F B n a i -
    masked B.threshold ((F i).footprint (0:Site n)) ((rack n F a full).dataF i)

variable {σ C : ℝ} (hf : ∀ i,(F i).Invariant) (hX : SumBudget (fun i=>(F i).budget σ) C) (h : 0 < σ)
variable {n}

include hf
lemma loosen (i : ℕ) : let f := Frame.deficit F B n a i; let t:= B.threshold; let S:= rosebud F n i
    GaugeInvariant f ∧ Measurable f ∧ UsesFinal t S f ∧ ∀ x,Healthy t S x→ f x=0 := by
  intro f t S
  let D:= F i; let X:=D.footprint (0:Site n); let Y:=halo 2 {(0:Site n)}; let L:=recipe a full i; let g:=L • pollen (0:Site n) D
  have hg : B.Regular Y g := by
    apply AnalyticBridge.CouplingShape.reg_scale; apply reg_bill (bud_bill (0:Site n) D B) _ (fertile (0:Site n) (F i))
    · intro k U; unfold pollen tag; simp only [petals_gauge]; apply hf
    unfold pollen tag Atom.poly; fun_prop
  have hr:= (rose_era F n a full hf B).regular i; have hC:= (bandFits (n:=n) F a full hf B).regular i
  have he : X⊆S:= subset_union_left; have hp:Y⊆S:=subset_union_right
  exact ⟨fun k U=> congrArg₂ Sub.sub (congrArg₂ (·+·) (Mirrors.masked_gauge _ _ _ hr.symmetry k U) (Mirrors.masked_gauge _ _ _ hg.symmetry k U))
     (Mirrors.masked_gauge _ _ _ hC.symmetry k U), ((masked_measurable _ _ _ hr.borel).add (masked_measurable _ _ _ hg.borel)).sub (masked_measurable _ _ _ hC.borel),
     fun U V ha hx=> congrArg₂ (·-·) (congrArg₂ (·+·) (Mirrors.masked_reads B hr.sites U V ha hx) (Work.H03.reads_larger hp (Mirrors.masked_reads B hg.sites) U V ha hx))
       (Work.H03.reads_larger he (Mirrors.masked_reads B hC.sites) U V ha hx), fun x hx=>by
        change masked t S ((makeRose F n a full).dataF i) x + masked t Y g x - masked t X _ x = 0
        rw [masked_eq _ _ _ _ hx,masked_eq _ _ _ _ (healthy_mono hp hx),masked_eq _ _ _ _ (healthy_mono he hx)]
        simp only [makeRose,rack, Frame.echo,g,L,D,baseLine,Pi.sub_apply, Pi.smul_apply,smul_eq_mul]; ring⟩ -- syntax ..
lemma gift (i U) : |Frame.deficit F B n a i U|≤ 2*fairFee F a full B i := by
  have hh:= (rose_era F n a full hf B).charge i; have hz:= (bandFits (n:=n) F a full hf B).charge i
  let S:= rosebud F n i
  by_cases he:Healthy B.threshold S U
  · rw [(loosen F B a hf i).2.2.2 U he,abs_zero]; exact mul_nonneg zero_le_two hh.1
  have aux {q : ℝ} {T : Support n} {f : Config G n→ℝ} (h:B.supBounds (0:Site n) T f q) : |masked B.threshold T f U| ≤ q:= by
    by_cases hi:Healthy B.threshold T U
    · rw [masked_eq _ _ _ _ hi]; exact h.2 U hi [] (by simp) (by simp)
    rw [masked_ne _ _ _ _ hi,abs_zero]; exact h.1
  simp only [Frame.deficit,pollenMark,Pi.sub_apply,Pi.add_apply]; refine (abs_sub ..).trans ((add_le_add ((abs_add_le ..).trans (add_le_add (aux hh) (aux ((AnalyticBridge.CouplingShape.sup_scale _ (Bill.sup (bud_bill (0:Site n) (F i) B) fun V h=>healthy_mono (show {(0:Site n)}⊆halo 2 {(0:Site n)} from halo_subset ..) h)))))) (aux hz)).trans_eq ?_)
  unfold fairFee; ring

def pours (V : Type) [DecidableEq V] (R : Census V) (X : V→Type) : Leftovers R X G n:=
    ⟨⟨(fun i=> shelf (Frame.makeRose F n a full) i |>.support) ∘ numbering _,(fun i:Cycle n=>Frame.deficit F B n a i.2 ∘ i.1.view) ∘ numbering _⟩,fun _ _ _=>0⟩

variable {V : Type} [DecidableEq V] {R : Census V} {X : V→ Type} [∀ i,NormedAddCommGroup (X i)] [∀ i,NormedSpace ℂ (X i)]
variable {O : Readers V X n} {w : V→ℝ}
lemma puts : Placed B O (Frame.pours F B a V R X):= by
  let N:=numbering (Cycle n); let D:=shelf (Frame.makeRose F n a full)
  let f:= Frame.pours F B a (n:=n) V R X
  have hv (i : Cycle n) := loosen F B a (n:=n) hf i.2
  refine ⟨fun i=> ⟨_,(D (N i)).anchor⟩,⟨fun i U h=> (hv (N i)).2.2.2 _ (Seat.healthy (N i).1 _ _ U|>.mp h),
    fun i=> Push.Local.invariant_pull (hv (N i)).1 _ _,fun i=> (hv (N i)).2.1.comp (continuous_pull ..).measurable,
    fun i=>Push.Local.uses_pull (hv (N i)).2.2.1 _ _,fun s b=> ?_⟩,fun _=> ⟨fun _ _ _=>rfl, fun _=>measurable_const,fun _ _ _ _ _=>rfl,fun _ _=> carry_zero⟩,fun _ _ _=>rfl,fun _ _ _ _=>rfl,fun _ _=>Testing.Catalogue.empty⟩
  let X:= Equiv.prodCongr (Seat.move s b) (Equiv.refl ℕ); let u:= (N.trans X).trans N.symm
  have he i:N (u i)=X (N i):= N.apply_symm_apply _
  refine ⟨u, fun i=> ?_,fun i U=> ?_⟩
  · change (D (N (u i))).support=_; rw [he]; exact Seat.spread_move ..
  change Frame.deficit F B n a _ ((N (u i)).1.view U)=_
  rw [he]; change Frame.deficit F B n a _ (((Seat.move s b) (N i).1).view U)=_; rw [Seat.view_move]; rfl

include h hX
variable {B}
omit [∀ v,NormedSpace ℂ (X v)] in
lemma fruit {e : ℝ} (he:0≤e) (hp : (later B (e+2) (by linarith)).supportExponent / B.B ≤ σ/4) (hb: 2 ≤ B.B) :
    let D:=later B (e+2) (show 0≤e+2 by linarith)
    let z := cost D*(roseCharge a σ G D*C)
    Compensated B O (Frame.pours F B a V R X) w e
      (Footprint.payment 1 (4*B.B+2) 0 1 (2/(turnFee D)) z (B.supportExponent+e) 0) := by
  intro D z
  let A:= makeRose F n a full; let f:= Frame.pours F B (n:=n) a V R X; let N:= numbering (Cycle n); let Y:=A.shelf
  let L v:= fairFee F a full D (N v).2; let d:=turnFee D
  let c v:= d*L v
  have hd : 0 < d:=turnFee_pos D
  have hv x: SumBudget (fun i=> if (Y (N i)).site=x then D.mass (Y (N i)).support (c i) else 0) z:=
    Cost.equiv N (totals (in_time F n a h hp hb full hX) x)
  have hp i : 0 ≤ L i:= ((rose_era F n a full hf D).charge (N i).2).1
  have hx i : 0 ≤ c i:=mul_nonneg hd.le (hp i)
  let o v:= (Y (N v)).site; let g v := coverNumber B.B (Y (N v)).support; let K:= f.real.region
  have he': Footprint.Anchored o c g (D.supportExponent) z := by
    intro x; convert hv x using 2 with i; unfold o; split_ifs; exact mul_comm ..; rfl
  let u i:= 2*L i
  have hg: Footprint.reserve D.supportExponent (B.supportExponent+e) 1 1:= ⟨by linarith [B.exponent_pos],zero_lt_one,by simp only [D,later]; linarith⟩
  have hr (i) (x : Site n) (hv:x∈K i): separation x (o i) ≤ (4*B.B+2)*(1+g i):= by
    have hj:=Corona.extent (K i) B.B hv (Y (N i)).anchor; change separation x (o i) ≤ g i*(4*B.B+2)+2*B.B at hj; linarith only [hj]
  have hK i: (coverNumber B.B (K i):ℝ) ≤ 0+(1:ℝ)*g i:= by unfold K f pours g; simp; rfl
  have hh := Footprint.assigned id 1 (fun s : Support n=> by simp) o c hx g K he' _ 0 _ hr hK (C:=2/d) (by positivity) hg u (fun i=>mul_nonneg zero_le_two (hp i)) fun i=> le_of_eq (by unfold u c; field_simp)
  have hk : Over (0:Poly R) 0:=by simpa using (over_unit (R:=R)).scale (s:=0) (t:=0) (by simp)
  refine ⟨u,fun _=>0,fun i U=> ?_,fun _=>carry_zero,fun _=>rfl,fun _ _ _ _=>hk,?_⟩
  · exact gift F B a hf (N i).2 ((N i).1.view U)
  simp only [Poly.zero_price,add_zero]; exact hh
end YM.Comparison.Density.Render.Frame
