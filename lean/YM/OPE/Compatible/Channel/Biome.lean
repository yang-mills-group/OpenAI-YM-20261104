import YM.OPE.Compatible.Channel.Letters
/-!
# Color actor - point and volumes
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Set Lattice Laurent MeasureTheory RG Finset Next.Free Bloch Precision Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Carrier Work.F08 Matrix Exterior
open scoped Topology BigOperators Classical
variable {r n m j k:ℕ}{L c f:Side}{η U C:ℝ}
namespace Script
open Page
variable {W:Type*}[Fintype W] [DecidableEq W]
abbrev Palette (W:Type*):= Axis × W
def chrome (W:Type*) [DecidableEq W](A:Lines L): Cross L (Palette W) (Palette W):= fun i j z=> if i.2.2=j.2 then A (i.1,coord i.2.1) (coord j.1) z else 0
abbrev ringList (i:Ink (Palette W) n)(l:Fin n):= (i l).1
abbrev ringTone (i:Ink (Palette W) n)(l:Fin n):= (i l).2
omit [Fintype W] in
lemma chrome_cost {A:Lines L}(h:A.strip η C)(hc:0 ≤ C): (chrome W A).strip η C:=by
    intro x y; unfold chrome; by_cases hv:x.2.2=y.2; simp only [hv,if_true]; exact h ..
    simp [hv,Width,SumBudget,hc]
omit [Fintype W] in
lemma chrome_sum {A:Lines L}(h: Whole A): Whole (chrome W A):=by
   obtain ⟨η,C,h,hC⟩:=h; exact ⟨η,max C 0,h,chrome_cost (strip_mono hC le_rfl (le_max_left ..)) (le_max_right ..)⟩
omit [Fintype W] in
lemma call_chrome {A:Lines L}(a b: Ink (Palette W) r) (i:Cover)(x y: Bin r):
   call (chrome W A) i (syn x a) (syn y b) = if ringTone a=ringTone b then parcelK (fun _=>A) (ringList a) (ringList b) (fun _=>i) x y else 0:=by
      split
      next h=>
          unfold call parcelK; apply prod_congr rfl; intro j _; unfold linePay chrome; rw [if_pos]; rfl; exact congr_fun h j
      next h=>
          unfold call; obtain ⟨j,hj⟩:=not_forall.mp (show ¬ ∀ i,ringTone a i=ringTone b i from fun g=>h (funext g)); exact prod_eq_zero (mem_univ j) (show linePay _ _ _ = 0 from if_neg hj)
lemma pay_div (A:Lines L)(h:Whole A){p:Script (Palette W) r}(hp: soot m p U)(a:Cover)(b:Ink (Palette W) r) : sliceP (countermove (chrome W A) a p) b =∑ i:Ink (Palette W) r,(if ringTone i=ringTone b then courier (parcelK (fun _=>A) (ringList i) (ringList b) (fun _=>a)) (sliceP p i) else 0):=by
   let t(i:Ink (Palette W) r) := parcelK (fun _=>A) (ringList i) (ringList b) (fun _=> a)
   let e:Ink (Palette W) r × Bin r≃ Page (Palette W) r:= Equiv.trans (Equiv.prodComm ..) (blurb ..)
   ext1 x
   obtain ⟨σ,C,hσ,hC⟩:= chrome_sum (W:=W) h
   have hh: Summable fun i=>p i*call (chrome W A) a i (syn x b) := ((cashmoves hC hσ p a hp).collectible (payer m) (syn x b)).of_norm -- bbox
   unfold sliceP at *; simp only [countermove,← e.tsum_eq (fun i=>p i*call (chrome W A) a i (syn x b)),Finset.sum_apply]
   let f(i):=p i*call (chrome W A) a i (syn x b)
   have hs := e.summable_iff.mpr hh; change Summable (f ∘ e) at hs
   change (∑' i,(f ∘ e) i)=_; rw [hs.tsum_prod,tsum_fintype]; refine sum_congr rfl fun i _=>?_ ; change (∑' z:Bin r,p (syn z i)*call (chrome W A) a (syn z i) (syn x b)) = (if (ringTone i=ringTone b) then _ else (0: Bin r→ℝ)) x
   simp_rw [call_chrome]; split_ifs with hx; rfl; simp

end Script
end YM.OPE.Flume
