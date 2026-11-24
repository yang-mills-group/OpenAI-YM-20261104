import YM.Gaps1020.Local.Production
import YM.RG01.Survive.Coupled
/-!
# Pre-reset complete E/K norm for the expansion

Expose the *full* `Collection.Local` rather than losing its exponent payment
when presenting the RG01 analytic consumer.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GapsLocal.Vacuum
open Function Filter Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Control Window Coat Footprint Raw Matter
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Stained Shield
open PhysicalNext PhysicalNext.Repeat Height Greenbelt
open Gas Ursell Trees RG.Supply Org Roost Opera
open AnalyticBridge VerifiedReset Collection Extra.Iteration Match Song Refrain Geo Quotes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side}{H:Listing G c} {d : BudgetPoint} {s μ C W : ℝ}
variable {S : StepData c f} {T : Tube G S} {P : Teller G} {R : RG.Rep G f}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}

lemma choirMoves (H:Cash W s μ L Q o C T R) (π : Alliance H H 1 0) (g: Magazine H → Config G c→ℝ) (γ:ℝ)
    {V:Collection.Source G c}(he:V.logRead= choir g ∘ pennant H)(hv:V.hardRead=(plusone H π χ γ).hardRead)
    (t:Signed)(x:Site c):Nonempty (((posting d H).read V).Moves t x):=by
  obtain ⟨ρ⟩ := H.laws.intake.cap.labels.moves t (S.ratio.embed x)
  obtain ⟨η,hη⟩ := settles H π χ t x ρ
  let e := whirl (ι:=Magazine H) t x; let a:=pennant H; let k:=Refrain.badge H
  have hk i : k (congo k η i)=_ := perch k η i; have ha i : a (congo a e i)=_ := perch a e i
  let h i:= spirit (scaleT d H) g t x i
  unfold Listing.read; rw [he,hv]
  refine ⟨⟨congo a e,congo k η,fun i=>?_,fun i=>?_,fun i=>?_,fun i=>?_,fun i V=>?_,fun i V=>?_,fun i V=>?_⟩⟩
  · change (revolve _ (a (congo a e i))).site=_; rw [ha]; exact (h _).1
  · change (revolve _ (a (congo a e i))).support=_; rw [ha]; exact (h _).2.1
  · change (reserve H (k (congo k η i))).support=_; rw [hk]; exact (hη _).1
  · change (reserve H (k (congo k η i))).inventory=_; rw [hk]; exact (hη _).2.1
  · change (reserve H (k (congo k η i))).extraTest V ↔ _; rw [hk]; exact ((hη (k i)).2.2 V).1
  · change choir g (a (congo a e i)) V=_; rw [ha]; exact congr_fun (h (a i)).2.2 V
  change fuse H π χ (k (congo k η i)) V=_; rw [hk]; exact ((hη (k i)).2.2 V).2

variable {x y z : Collection.Source G c}{a b w a' b':ℝ}
lemma subLocal (hx : Collection.Local H d x a w)(hy : Collection.Local H d y b w)
    (hg:z.logRead=x.logRead-y.logRead)(he:z.hardRead=x.hardRead)(hp:∀ s b, Nonempty ((H.read z).Moves s b)):
    Collection.Local H d z (a+b) w:=by
  obtain ⟨f,hf,hF⟩:=hx.cheap; obtain ⟨g,hg',hg₀⟩:=hy.cheap
  refine ⟨fun i=> by rw [hg]; exact reg_sub (hx.smooth i) (hy.smooth i), ?_,hp,⟨fun i=> f i+g i,?_,?_⟩,?_⟩
  · have h:= hx.family; unfold Listing.read at *; rw [he]; exact ⟨h.sym,h.symtest,h.meas,h.meas_test,h.reads,h.reads_test,h.permit⟩
  · intro i; rw [hg]; exact sup_sub (hx.smooth i) (hy.smooth i) (hf i) (hg' i)
  · intro i; convert! budget_plus (hF i) (hg₀ i) using 1; ext k; split_ifs <;> ring
  rw [he]; exact hx.expensive
lemma addLocal (hx : Collection.Local H d x a w)(hy : Collection.Local H d y b w)
    (hg:z.logRead=x.logRead+y.logRead)(he:z.hardRead=x.hardRead)(hp:∀ s b, Nonempty ((H.read z).Moves s b)):
    Collection.Local H d z (a+b) w:=by
  obtain ⟨f,hf,hF⟩:=hx.cheap; obtain ⟨g,hg',hg₀⟩:=hy.cheap
  have hh (i:ℕ): z.logRead i = x.logRead i - (-1:ℝ) • y.logRead i := by rw [hg]; simp
  refine ⟨fun i=> by rw [hh]; exact reg_sub (hx.smooth i) (CouplingShape.reg_scale _ (hy.smooth i)), ?_,hp,⟨fun i=> f i+g i,?_,?_⟩,?_⟩
  · have h:= hx.family; unfold Listing.read at *; rw [he]; exact ⟨h.sym,h.symtest,h.meas,h.meas_test,h.reads,h.reads_test,h.permit⟩
  · intro i; rw [hh]; apply sup_sub (hx.smooth i) (CouplingShape.reg_scale _ (hy.smooth i)) (hf i); simpa only [abs_neg,abs_one,one_mul] using! CouplingShape.sup_scale (-1) (hg' i)
  · intro i; convert! budget_plus (hF i) (hg₀ i) using 1; ext k; split_ifs <;> ring
  rw [he]; exact hx.expensive
lemma liftLocal (hx : Collection.Local H d x a b)(h : a ≤ a')(h' : b ≤ b') : Collection.Local H d x a' b':= by
  obtain ⟨f,hf,hF⟩:=hx.cheap; obtain ⟨g,hg,hG⟩:=hx.expensive; exact ⟨hx.smooth,hx.family,hx.transforms,⟨f,hf,fun i=>budget_loosen (hF i) h⟩,⟨g,hg,fun i=>budget_loosen (hG i) h'⟩⟩
lemma sung (H:Cash W s μ L Q o C T R) (g h: Magazine H → Config G c→ℝ) :
    choir g ∘ pennant H + choir h ∘ pennant H = choir (g+h) ∘ pennant H := by
    funext i V; simp only [Function.comp_apply,choir, Pi.add_apply,Pi.smul_apply, smul_eq_mul]; ring
end YM.GapsLocal.Vacuum
