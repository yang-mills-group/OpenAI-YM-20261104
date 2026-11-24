import YM.Contacts.Procession.Slide
import YM.PertExtension.PTBills
/-!
# Birth prices.Mark gauge epoch through all orders on standard periodic tori

Wilson Section version. Adapts `PertExtension/BareSlot` proof of min valuation for using exponent charts to every full physical period, used now on the Wilson epoch off regulated volume projection.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace YM.Contacts.Procession.Welcome.Birth
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Laurent
open MeasureTheory Labels Source Drops Analysis Finset Bloch Push.AbsoluteSums Extra.Iteration MergeProof Next.Free Work.F08 Pulse Spine Origin Bid
open Milling Milling.Steam Milling.Forge Milling.Garf
open PertExtension.Series Radial Tested
open scoped Classical Topology BigOperators NNReal Matrix ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{X Y ι: Type}[Fintype ι]{k m d b:ℕ}{n: Side}
local notation "K"=> Link G n
def notice (s:RG.Slot)(i:G.ColorIndex) (x:K) := s.eval (expandAt 0 (input G n x)) i
lemma traveling (w:Lattice.Walk)(x:Site n) : Army (fun p:K=>fun _:Unit=> travel (input G n p) x w) 0:= by
   induction w generalizing x with
   | nil=> exact fun _=>contDiffAt_const
   | cons i w ih=>
      let f p:= input G n p; have hf: Army f 0:= Army.powL contDiffAt_id; apply Army.mul (v:=fun p:K=>fun _:Unit=>travel (f p) (x+i.vec) w) (u:=fun p:K=>fun _:Unit=> i.read (f p) x) ?_ (ih (x+i.vec)); intro j; unfold Step.read; split; exacts [hf.inv _,hf _]
lemma notice_cont (s:RG.Slot)(i:G.ColorIndex) : ContDiffAt ℝ ω (notice (n:=n) s i) 0:= by
  let f : K→ CoverConfig G:= fun p=> expandAt 0 (input G n p); let h (w:Lattice.Walk)(x:Cover): ContDiffAt ℝ ω (fun y => G.mat (travel (f y) x w)) 0 := by simp_rw [show ∀ y,travel (f y) x w=travel (input G n y) (wrap n x+0) w from fun y=> travel_at 0 (input G n y) x w]; exact traveling w _ ()
  let v : K→ G.El := fun x=>faceValue (f x) (s.offset,s.plaq); have hb : ContDiffAt ℝ ω (fun x=>G.mat (v x)) 0 := h ..
  let g (x) := G.mat (travel (f (x:K)) 0 s.walk); let Q:=LinearMap.toContinuousLinearMap G.projectColor; let M:=LinearMap.toContinuousLinearMap G.colorMat
  have H : ContDiffAt ℝ ω (fun x=>G.curvature (v x)) 0 := by
    unfold Gauge.curvature; simp_rw [G.mat_inv]; have hp:= hb.sub (((starL ℝ : G.Mat ≃L[ℝ] G.Mat).contDiff.contDiffAt).comp _ hb); exact Q.contDiff.contDiffAt.comp _ (hp.const_smul (1/2:ℝ))
  have hy: ContDiffAt ℝ ω (s.eval ∘ f) 0:= Q.contDiff.contDiffAt.comp _ (g:=Q) (f:=fun x=> g x*M (G.curvature (v x))* star (g x)) (((h _ _).mul (M.contDiff.contDiffAt.comp _ H)).mul (((starL ℝ : G.Mat ≃L[ℝ] G.Mat).contDiff.contDiffAt).comp _ (h _ _)))
  exact (EuclideanSpace.proj (𝕜:=ℝ) i).contDiff.contDiffAt.comp (f:=s.eval ∘ f) _ hy
lemma notice_zero (s:RG.Slot)(i:G.ColorIndex) : notice s i (0:K)=0:= by
   let H:=Next.Foundations.hol G; suffices h : expandAt (0:Site n) (input G n 0)=(1:CoverConfig G) by unfold notice; rw [h]; unfold RG.Slot.eval faceValue; rw [Pressure.one,Pressure.one,G.curvature_unit,map_zero]; rfl
   simp; rfl
variable {F:Labels.Frame G d}(C: SectionData F)
def threshold (C:SectionData F)(v:F.Index)(x:Config G n) := (C.places (Pi.single v 1) 0 x).re
def entry (v:F.Index)(x:K):= Birth.threshold C v (input G n x)
private lemma repr {i : F.Index} (p:Pose G m)(B:Fin m→RG.Slot) (h:C.evaluate (Pi.single i 1)=lumin p ∘ mapped B) (x:K) :entry C i x=(∑ d∈p.support,(MvPolynomial.coeff d p) * ∏ r∈d.support, ((notice (B r.1) r.2 x):ℂ)^(d r)).re := by
 change (C.evaluate _ (expandAt 0 _)).re = _
 rw [h, Function.comp_apply, Bid.lumin, MvPolynomial.aeval_eq_eval₂Hom, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq]; rfl
lemma gate (H:pop C)(i:F.Index) : AnalyticAt ℝ (entry C i (n:=n)) 0 ∧ ∀ (x:K) j,j < (F.grades i).2 → jet (entry C i) j x=0:= by
   obtain ⟨m,B,hS,p,hp,hq⟩:= H i; have h:AnalyticAt ℝ (entry C i (n:=n)) 0:= by
      rw [funext (Birth.repr C p B hp (n:=n))]; exact (Complex.reCLM.contDiff.contDiffAt.comp _ (.sum fun d _=> contDiffAt_const.mul <| contDiffAt_prod fun i _=> ((Complex.ofRealCLM.contDiff.contDiffAt.comp _ (notice_cont (B i.1) i.2))).pow ..)).analyticAt -- names
   refine ⟨h,fun x=>?_⟩; apply Milling.marker h -- number
   let u (a:Fin m×G.ColorIndex)(t:ℝ):ℂ:= Complex.ofReal (notice (B a.1) a.2 (t•x)); let k:=(F.grades i).2; let f (r:ℝ) := ∑ d∈p.support, (MvPolynomial.coeff d p) * ∏ i∈d.support, u i r^(d i)
   simp_rw [Birth.repr C p B hp]; suffices H : Bill k f from (by obtain ⟨r,hr,H⟩:= H; exact ⟨r,hr,H.mono fun t ht=> le_trans (Complex.abs_re_le_norm (f t)) ht⟩)
   suffices h : Bill k (∑ d∈p.support, (fun t :ℝ =>MvPolynomial.coeff d p*((∏ i∈d.support,u i ^ (d i)) t))) by
      convert h using 1; funext t; simp [Finset.sum_apply, Finset.prod_apply,f]
   apply bill_sum; intro j hj; have h i: Bill 1 (u i):= by obtain ⟨C,hC,he⟩:= zero_first ((notice_cont (B i.1) (G:=G) i.2).of_le le_top) (notice_zero (B i.1) i.2) x; exact ⟨C,hC,he.mono fun r hr=>by simpa [u] using! hr⟩
   have hs := bill_product j.support (fun i=>j i*1) _ (fun i _ => bill_pow (h i) (j i)); refine bill_ge (bill_mul (bill_const (MvPolynomial.coeff j p)) hs) ?_; simpa [Finsupp.sum] using hq _ hj
end YM.Contacts.Procession.Welcome.Birth
