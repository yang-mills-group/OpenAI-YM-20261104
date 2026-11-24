import YM.Contacts.Procession.Atlas
/-! # Pivots, aperture matrix before Wick normalization. Include one Mark, no source align bound. -/
noncomputable section
namespace YM.Contacts.Procession.Cartons
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix
open MeasureTheory Labels Source Drops Analysis Finset Bloch Laurent Push.AbsoluteSums Extra.Iteration MergeProof Next.Free Work.F08 Pulse Spine Origin
open Milling Milling.Steam Milling.Forge Milling.Garf Tensor MultiNext.SignedSource Pattern Shuttle Tide
open scoped Classical Topology BigOperators NNReal ENNReal Matrix ContDiff Matrix.Norms.Frobenius
open Morning Mediator Next.Foundations
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 90000
set_option autoImplicit false
variable {G:Gauge}{X Y: Type}{m:Side}{F:Cohort G}{d k h u n:ℕ}(B: Labels.Frame G d)
-- read on entire Mark.App.No power prices assumed.
open Planned.PrimaryIntegral295 WardBin Push.Local Catch Welcome Lumen Larch Sun
open Welcome.Birth Next.Free
variable {B}{P : SectionData B}{X:bore G}{p i :ℕ}{x:B.Index}{H:Hol G}{y:Dye G}
lemma shipper (h: Paints P X x p)(hx: (B.grades x).2 ≤ p)(he:Bid.pop P) (m:Side) : Tide.Ticket (Birth.entry (n:=m) P x) (coil X p (p+4-(B.grades x).2)) d := by
   refine ⟨(Birth.gate P he _).1,fun j hj x'=>?_ ⟩; by_cases hi:(B.grades x).2 ≤ j; · unfold coil Resetter.dazzle shiftA; rw [if_pos (by omega),if_pos (by unfold Catch.cap; omega)]; exact ((h.wanted _ _ _ _).trans (if_pos (by unfold Catch.cap; omega))).symm
   have hz:= h.void _ (lt_of_not_ge hi) x'; unfold coil Resetter.dazzle shiftA; split; split; unfold Catch.cap at *; omega; rw [hz]; simp [House.design_spec,packing,cram]; rw [hz]; simp [House.design_spec,packing,cram]
private lemma real_label {t:B.Index}(hp:P.Sound H)(v: CoverConfig G): ( (P.evaluate (Pi.single t 1) v).re:ℂ)=P.evaluate (Pi.single t 1) v:= by
    let p:= P.evaluate (Pi.single t 1) v; have he: ∀ z:ℂ, star z=z → (z.re:ℂ)=z:=fun z h=> by apply Complex.ext; rfl; have hx:= congr_arg Complex.im h; change -z.im=z.im at hx; simp; linarith
    apply he; rw [←hp.ordinary_real]; apply congr_arg (fun w=>P.evaluate w v); funext t'; by_cases he:t'=t <;> simp [he]
lemma height_snap (h:Paints P X x p)(hx:(B.grades x).2 ≤ p)(he:Bid.pop P)(hP:P.Sound H)(q:G.ColorIndex) : let V:=coil X p (p+4-(B.grades x).2); Shape B (panel V d (d*(d+1)) d) (Pi.single x 1):= by
   intro V; constructor; rintro ⟨J,j⟩; rw [Push.Local.runProbe_eq]; let T:= Barrage.Slope.terraceP; have atT:= Barrage.Slope.stepping; let A i:= Birth.threshold P x (n:=T i); have hp(i:ℕ): GaugeInvariant (A i):=fun u v=> congr_arg Complex.re (P.placed_invariant hP (0:Site (T i)) (Pi.single x 1) u v); let hV:= Catch.coil_tags h.mount ((h.chip ( (Exterior.coord 0),q) 1).choose_spec) (zero_lt_one) (p+4-(B.grades x).2) -- names
   let f := fun t=> Labels.read (scaleJet J t) (B.coords.symm (Pi.single x 1)).val; have hj:= Nat.le_of_lt_succ j.isLt; let g i:= ((A i ∘ input G (T i)) ∘ north (h:=d) H (T i)) ∘ plank G d ∘ glide J d;
   let h': Tendsto (fun i=> iteratedDeriv j.val (g i) 0) atTop (𝓝 (Rod V d (d*(d+1)) d (J,j))) := juice Barrage.Slope.stepping H (fun i=> shipper h hx he (T i)) hV.toFelt J hj ((Nat.mul_le_mul_right _ hj))
   have hZ:∀ᶠ i in atTop, Complex.ofRealCLM (iteratedDeriv j.val (g i) 0)=iteratedDeriv j.val f 0:= by
      filter_upwards [(eventually_all_finset P.stencil (p:=fun a i=> lift (wrap (T i) a) = a)).2 (fun i _=>eventually_unfold T atT i)] with i hX; let F:= Birth.entry (n:=T i) P x; let R:B.Coeff:=Pi.single x 1; have hf: ∀ t, ((A i (H.testLinks d 0 J t) : ℝ):ℂ) = P.evaluate R (H.links d J t):= by
          intro t; refine Eq.trans (real_label (t:=x) hP (expandAt (0:Site (T i)) (H.testLinks d 0 J t))) (P.cylinder_local R _ _ (fun x hv hz=>?_)); change H.testLinks d 0 J t (wrap _ x.1+0,x.2)= _; simp [Hol.testLinks,hX _ (mem_coe.mp hv)]
      let K:= plank G d ∘ glide J d; have he:K 0=0:= (by unfold K; simp); have hd:=glide_ever d J; have hh: ContDiffAt ℝ ω K 0:= ((plank G d).contDiff.comp hd).contDiffAt; let g':=(A i ∘ input G (T i)); have hx: ContDiffAt ℝ j.val (g i) 0:= by
           apply ContDiffAt.of_le (n:=ω) _ le_top; refine ContDiffAt.comp (f:=K) (g:=(F ∘ north H _)) _ ?_ hh; rw [he]; refine ContDiffAt.comp _ ?_ (north_diff _ H d); rw [north_zero]; exact (shipper h hx ‹Bid.pop P› (T i)).1.contDiffAt
      let X:= ahead (A i) (hp i) H J d; let U:= (hP.projects R J).2.2 _ hj; have hw: Complex.ofRealCLM ∘ g i=ᶠ[𝓝 (0:ℝ)] (fun h=>P.evaluate R (H.links d J h)):= X.mono fun b hb=> (show Complex.ofRealCLM _ = Complex.ofRealCLM _ from congr_arg _ hb.symm).trans (hf b); exact (DFunLike.congr_fun (Complex.ofRealCLM.iteratedFDeriv_comp_left hx (i:=j.val) le_rfl) _).symm.trans ((hw.iteratedDeriv_eq j.val).trans U)
   exact tendsto_nhds_unique ((tendsto_const_nhds (x:=iteratedDeriv j.val f 0) (f:=atTop (α:=ℕ))).congr' (hZ.mono fun i hi=> Eq.symm hi)) (Complex.ofRealCLM.continuous.continuousAt.tendsto.comp h')
-- no negative order.Frame grading
lemma print_basis (h: Paints P X x p)(hx:(B.grades x).2 ≤ p)(he:Bid.pop P)(hP:P.Sound H)(q:G.ColorIndex)(v:B.Index)(i:ℕ): fill B p X i v=if i=0∧x=v then 1 else 0:= by
    let a:= (B.grades x).2; let b:= (B.grades v).2; unfold fill; split
    next h' =>
        let Y:=p+4+i-b; by_cases hn:p+4+i-b=p+4-a
        · unfold velum; rw [hn,(height_snap h hx he hP q).won]; by_cases hz:x=v; · subst v; have ht : a=b := rfl; have hk:i=0:= (by omega); simp [hk]
          simp [hz,Pi.single_eq_of_ne (Ne.symm hz)]
        rw [if_neg (fun ⟨hp,hx⟩=> hn (by unfold b a at *; rw [hp,add_zero,hx]))]; let F:=coil X p Y; have hg := h.mount; obtain ⟨t,ht⟩:=h.chip ((Exterior.coord 0),q) 1; refine vela_silent (coil_tags hg ht (by norm_num) Y) _ (fun j hj=>?_); unfold coil Resetter.dazzle shiftA; split; split; exact h.rank _ _ (by unfold Y b Catch.cap a at *; omega); rfl; rfl
    next h' => rw [if_neg]; rintro ⟨hi,hk⟩; rw [hi,add_zero,← hk] at h'; exact h' hx
variable (B)
-- pivot correction existence.Mode shape for ALL chosen frames before reexpression.Stencil actual.W.Calculator.
lemma letter_seed {H:Hol G}{P:SectionData B} (he:Bid.pop P)(hp:P.Sound H)(x:G.ColorIndex)(v:B.Index)(p:ℕ)(hq:(B.grades v).2 ≤ p) : ∃ X, Paints P X v p ∧ ∀ i:ℕ,∀ y:B.Index, fill B p X i y=if i=0 ∧ v=y then 1 else 0:= by obtain ⟨X,hX⟩:= Birth.artists P hp he v p hq; exact ⟨X,hX,fun i y=> print_basis hX hq he hp x y i⟩ -- remove line taut
end YM.Contacts.Procession.Cartons
