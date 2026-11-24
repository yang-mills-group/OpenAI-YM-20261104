import YM.LocalTaylorR2.Marker.Usage
/-!
 # Expenditure via Berths/Keeper, not a hypothesis of nonempty Slots.
 Collect Taylor estimates AFTER publishing Primary.Residual. The post-ε
 threshold below replays bulk estimates on real p threshold without switching masks
 to plate display. Adapt from Local Raw and Merge Flavor. Numerical
 SectionData costs carried in outputs.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Marker
open Function Filter Finset Lattice Wilson RG Source Labels LocalTaylorR2
open Push Push.AbsoluteSums Gas Ovens PowerSeries Extra.Histories Progress.DirectedRecipe Next.Foundations Precision
open PhysicalNext PhysicalNext.Repeat Blush Planned.GuardedAtom Guard
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{c f n: Side}
variable {i j:ℕ} {o: Site n}{X: ℕ → Support n}{B : BudgetPoint} {σ C Λ a b e t r δ u u' v v' : ℝ}
    {F:Labels.Frame G i} {R : Rep G n}{ζ: ℕ→ Config G n→ℂ} {Y:Hol G}{T:Source.SectionData F}
open Local
lemma vacant : ForceFormat B (R.activities) o 0 := by refine ⟨by simp, by simp,fun i _ _=>rfl,fun i _ _ _ _=>rfl, fun i=> measurable_const⟩
lemma costless (h:0≤ e) : ForceCost B R.activities 0 e:= ⟨fun _=>0,by simp [BudgetPoint.mass, SumBudget,h]⟩
lemma larger (h: ForceCost B R.activities ζ a) (ht:a≤b): ForceCost B R.activities ζ b:=by obtain ⟨x,hx,H⟩:=h; exact ⟨x,budget_loosen hx ht,H⟩

variable {P L M : Push.Local.Raw F n}

structure Segment (P M L: Push.Local.Raw F n):Prop where
    seed : P.seed=M.seed+L.seed
    bulk : P.bulk=M.bulk+L.bulk
    force : P.forced=M.forced+L.forced

structure Hinge (S A B : Source.Coefficient F n):Prop where
    seed : S.x=A.x+B.x
    common : S.support=A.support ∧ S.support=B.support
    bulk : S.regular=A.regular+B.regular
    force : S.forced=A.forced+B.forced

namespace Modesty
variable {p : BudgetPoint}
lemma add (h : Segment P M L)(h1 : Modesty G p o X M.bulk u)(h2:Modesty G p o X L.bulk v): Modesty G p o X P.bulk (u+v) := by
    rw [h.bulk]; obtain ⟨w,hp',hw⟩:=h1.price; obtain ⟨b,hk,hb⟩:= h2.price
    refine ⟨(fun i=>regular_add (h1.regular i) (h2.regular i)),w+b,fun i=> bound_add (h1.regular i) (h2.regular i) (hp' i) (hk i),?_⟩
    simpa only [Local.reservedMass,mul_add,Pi.add_apply] using! budget_plus hw hb
lemma rise {p} (h:Modesty G p o X ζ e)(ht:e ≤ v): Modesty G p o X ζ v:=by obtain ⟨f,hf,H⟩:= h.price; exact ⟨h.regular,f,hf,budget_loosen H ht⟩
lemma sum {p} (h:Modesty G p o X ζ e): ∃ f:ℕ→ℝ,Summable f∧∀ i,p.supBounds o (X i) (ζ i) (f i):=by
    obtain ⟨f,hF,hS⟩:= h.price; have he i : f i ≤ reservedMass p (X i) (f i):=le_mul_of_one_le_left (hF i).1 (Real.one_le_exp (by have h:=p.exponent_pos; positivity))
    exact ⟨f,hS.2.1.of_nonneg_of_le (fun i=> (hF i).1) he,hF⟩
lemma lean {p} (h:Modesty G p o X ζ e) (U:Config G n): Summable (fun i=>masked p.threshold (X i) (ζ i) U):=by
    obtain ⟨f,hf,hp⟩:= h.sum; refine Summable.of_norm_bounded hf fun i=>?_; by_cases he: Healthy p.threshold (X i) U; rw [masked_eq _ _ _ _ he]; exact (hp i).2 _ he [] (by simp) (by simp)
    rw [masked_ne _ _ _ _ he,norm_zero]; exact (hp i).1
end Modesty

variable (S: Berths R.p R.activities (fun i=> joint T o (X i))) (he: Readable Y T R.p n t)
-- restated proof-helper Slots using same supports and definitions, not crashing private names.
private abbrev glass (A:Activities G n) := { A with forced:=fun i=> {A.forced i with extraTest:=fun _ => True} }
private def cross (A : Activities G n) {ι : Type*} (X : ι → Support n) : Local.Letters (glass A) X ≃ Local.Letters A X :=
  Equiv.sigmaCongrRight fun _i => (Equiv.refl (Finset ℕ)).subtypeEquiv
    (fun _x => ⟨fun h => ⟨h.1,h.2,h.3⟩,fun h => ⟨h.1,h.2,h.3⟩⟩)
private def bridge (S : Berths R.p R.activities X) : Push.Local.Slots (glass R.activities) X where
  label := (cross R.activities X).toEmbedding.trans S.label
  support i := S.support ((cross R.activities X) i)
  inventory i := S.inventory ((cross R.activities X) i)
  allows _ _ := trivial
variable (h : Segment P M L)
include he S h
lemma hinge (h1 : M.Format o X R)(h2:L.Format o X R)(hu : Summable (M.row o X Y R.p.threshold))(hv: Summable (L.row o X Y R.p.threshold)): Hinge (Guard.mint S P Y) (Guard.mint S M Y) (Guard.mint S L Y):=by
   let S' := bridge S; let t:=R.p.threshold; let v(M:Push.Local.Raw F n):= M.row o X Y t; let p(M : Push.Local.Raw F n)(i):= primary T o t (v M i); let q(M:Push.Local.Raw F n)(i):= Local.residual Y T o (X i) t (M.bulk i); let R'(M:Push.Local.Raw F n)(i):= Local.rebate Y T o (X i) t (M.bulk i)
   have he'(i): v P i = v M i + v L i:=by unfold v Raw.row; rw [h.bulk, Pi.add_apply,weighted,project_add Y o (h1.regular i) (h2.regular i) he.order,map_add,map_add]; rfl
   have hq (i): q P i = q M i + q L i:= by change P.bulk i - presented T o t (v P i)=_; rw [h.bulk,Pi.add_apply,he',map_add,add_sub_add_comm]; rfl
   have hR' i : R' P i = R' M i+ R' L i:=by
     change masked t (X i) (P.bulk i) -p P i - masked t (joint T o (X i)) (q P i) = ( _ - p M i - _) +( _ -p L i - _)
     rw [h.bulk, Pi.add_apply,hq, show p P i = p M i + p L i from congr_arg (primary T o t) (he' i) |>.trans (map_add ..)]; funext U
     simp only [Pi.sub_apply,Pi.add_apply, breakT]; abel
   refine ⟨?_,⟨rfl,rfl⟩,funext hq,?_⟩
   · change P.seed + ∑' i, v P i= (M.seed+∑' i,v M i)+(L.seed+∑' i,v L i); simp_rw [h.seed,he']; rw [Summable.tsum_add hu hv]; abel
   change P.forced+S'.packLinear t (R' P)= (M.forced+S'.packLinear t (R' M))+(L.forced+S'.packLinear t (R' L))
   rw [h.force,show R' P=R' M+R' L from funext hR',map_add]; abel
omit he S
lemma pieces (T:SectionData F)(he:R.activities.KBound R.p a)(h1:Modesty G R.p o X M.bulk u)(h2:Modesty G R.p o X L.bulk v)
    (hv:ForceCost R.p R.activities M.forced u')(hw:ForceCost R.p R.activities L.forced v'): P.eval o X T R=M.eval o X T R+L.eval o X T R:=by
   funext U; simp only [Local.Raw.eval,Pi.add_apply,h.seed,h.bulk,h.force,map_add,breakT]; rw [Summable.tsum_add (h1.lean U) (h2.lean U), Summable.tsum_add ((dominated_gasMark hv he).summable U) ((dominated_gasMark hw he).summable U)]; ring

structure CanvasOut (P : Push.Local.Raw F n) (Y:Hol G)(T:SectionData F)(o:Site n)(X : ℕ → Support n)(R: Rep G n)(κ v t a b d:ℝ): Prop where
   format : P.Format o X R
   mass : Modesty G R.p o X P.bulk a
   packets : ForceCost R.p R.activities P.forced (κ*b)
   seed_zero : P.seed=0
   size : Local.factor Y T R.p.supportExponent t*a ≤ d
-- include none
namespace CanvasOut
variable (P) {κ : ℝ} (hr:R.Lawful σ C Λ δ v) (H:CanvasOut P Y T o X R (Real.sqrt v) v t a b r)
include H
omit h
lemma decked : Planned.GuardedAtom.Deck P o X R (Real.sqrt v) a b :=⟨by obtain ⟨e,hp,hq⟩:=H.mass.price; exact ⟨e,hp,hq⟩, H.packets⟩
include he
variable (hv:0<v)(hw: hitWidth R.p * Real.sqrt v ≤ 1)
include hv hw
lemma rooted : Tare P o X Y T R t v (Real.sqrt v) r b r:=by
   obtain ⟨⟨e,hp,hq,hv'⟩,hZ⟩:= Planned.GuardedAtom.Deck.usual hv hw he H.format (h:=decked P H)
   exact ⟨⟨e,hp,budget_loosen hq H.size,budget_loosen hv' (mul_le_mul_of_nonneg_left H.size (Real.sqrt_nonneg v))⟩,hZ⟩
 
lemma rows : Summable (P.row o X Y R.p.threshold) := (Extra.Histories.Size.series _ (((rooted P he H hv hw).row_cost he H.format).2.1)).of_norm
include hr S
lemma booked : let M := Guard.mint S P Y
    M.Format o Y R ∧ M.support=(fun i=> joint T o (X i)) ∧ M.density o T R=P.eval o X T R ∧
    Planned.GuardedAtom.Tab M o R (Real.sqrt v) r (b+r) ∧ F.coeffSize M.x ≤ r:= by
  intro M; have hh:=rooted P he H hv hw; have hk:=Real.sqrt_pos.mpr hv
  refine ⟨Guard.usage S H.format hr he,rfl,value_mint S H.format hr hk he hh, Guard.tab_mint S H.format hr hk he hh,?_⟩
  have ht:F.coeffSize 0=0:= by simp [Frame.coeffSize]
  simpa only [H.seed_zero,sub_zero,ht,zero_add] using! Guard.size_mint S H.format he hh 0
end CanvasOut
end YM.LocalTaylorR2.Marker
