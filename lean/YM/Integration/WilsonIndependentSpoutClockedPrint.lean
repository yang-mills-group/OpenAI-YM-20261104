import YM.Integration.WilsonIndependentSpoutFundedClocks
import YM.Integration.WilsonIndependentSpoutPaidAddon
import YM.Integration.WilsonIndependentSpoutSchurStory

/-! The elected physical circuit's primitive bank and the true earlier Wilson
interaction through the claimed finite order at their common reporting clock. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutClockedPrint
open Matrix PowerSeries Lattice RG WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank
open RegulatorIR RegulatorIR.Ledger RegulatorIR.Oracle RegulatorIR.Profiles RegulatorIR.Binding
open RegulatorIR.Prim RegulatorIR.Geometry RegulatorIR.Geometry.Field RegulatorIR.Diagram
open RegulatorIR.Diagram.Formal RegulatorIR.Older RegulatorIR.Ward RegulatorIR.Clocks
open RegulatorIR.Clocks.Warp RegulatorIR.Calibration RegulatorIR.Halo Tree FreeResolvent Metric Precision Exterior
open WilsonIndependentSpoutFundedClocks WilsonIndependentSpoutOrdinarySpring WilsonIndependentPublicFreeTrain
open scoped Classical BigOperators Matrix

private theorem square_power {A B:Cost}{p:ℕ}(h:Squares p A B)(k:ℕ):
    Squares p (A^k) (B^k):=by
  induction k with
  | zero=>intro i hi;simp
  | succ n hn=>simpa only [pow_succ] using hn.maintains h

theorem source {A B:Cost}{p:ℕ}(h:Squares p A B)(one:constantCoeff B=1)
    {V T:Type}[AddCommMonoid T][SMul ℝ T](P:Pal T V){e:ℕ}(he:e≤p):
    mix A P e=mix B P e:=by
  have hb:coeff 0 B≠0:=by rw [coeff_zero_eq_constantCoeff_apply,one];norm_num
  have ha:coeff 0 A≠0:=by rw [h 0 (Nat.zero_le p)];exact hb
  have hi:=inv_v h ha hb
  funext r
  unfold mix
  exact Finset.sum_congr rfl fun i _=>by rw [( (square_power h i).maintains (square_power hi r)) (e-i) (by omega)]

theorem field {G:Gauge}{c n:Side}(S:StepData c n)(F:Forest S.ratio)(H Y:FaceRow)
    (Q:Matrix (Body 1 n) (Body 1 c) ℝ)(Ñ:ChartRatio G)(V:PChart G n)
    {A B:Cost}{p:ℕ}(h:Squares p A B)(one:constantCoeff B=1){e:ℕ}(he:e≤p):
    coeff e (WilsonIndependentSpoutSchurFrame.field S F H Y Q A Ñ V)=
    coeff e (WilsonIndependentSpoutSchurFrame.field S F H Y Q B Ñ V):=by
  simp only [WilsonIndependentSpoutSchurFrame.field,map_add,map_sub,loom,coeff_map,Blue.flash,coeff_mk,
    source h one _ he]

variable {G:Gauge}{W:Type}{M:W→ℕ}{sides:Page M→Side}{K:KernelChoices}
    (C:Circuit M sides)(Z:∀P:Patch,P.Branches K G)(Y:Program K)
    (A:W→Levels G)(s:W→ℕ)

theorem original (simple:G.Simple)(inc:∀w,Matches (A w) C K (s w) w)(p:ℕ):
    let Ñ:=XSpace.Bare.chart G
    ∃D:Tent M,(∀w,D (Page.opening M w)=Calibration.dawn)∧∀(f:Flap M)(c:Side)(e:ℕ),
      0<e→e≤p→
      let N:=s f.volW+M f.volW;let m:=s f.volW+(M f.volW-(f.offset+1))
      let L:=A f.volW;let S:=mStep L c m;let F:=repeatF S;let Q:=roam L N m c
      let H:=freeForms L N (m+1);let H':=freeForms L N m
      let α:=relativeC L Ñ N (m+1) (N-(m+1))
      let rows:=C.bore G Z (sheet D) f;let V:=(story L Ñ N (m+1)).1 (c*(loose L m).L)
      ((C.dialect Y G Z (sheet D)).frames f).addon=many rows ∧
        ∀x:Lawn (Active G F⊕Woods G c),
          let z:=overM G S F *ᵥ x;let u:=camber G (extractV G S F Q) *ᵥ z
          let b:=rightArm z;let X:=joined u b
          MvPolynomial.eval x (coeff e (WilsonIndependentSpoutSchurFrame.field S F H H' Q α Ñ V))=
            MvPolynomial.eval u (coeff e (orbC (precisionC G (c*(loose L m).L) H)-Blue.flash (mix α V)))+
            (∑a:Edge (Site (c*(loose L m).L)),drums (rows (.inl (peg a)) e) e X)+
              ∑a:Edge (Site c),drums (rows (.inr (peg a)) e) (e+2) X:=by
  intro Ñ
  have ratio:LocalRatio Ñ:=XSpace.Bare.chart_ratio G
  obtain ⟨D,initial,pages⟩:=WilsonIndependentSpoutFundedClocks.original A Ñ s simple ratio p
  refine ⟨D,initial,?_⟩
  intro f c e pos hi N m L S F Q H H' α rows V
  have depth:=f.ok
  have AGE:age s f.prev=m+1:=by change s f.volW+(M f.volW-f.offset)=s f.volW+(M f.volW-(f.offset+1))+1;omega
  have DATE:N-(m+1)=f.offset:=by dsimp only [N,m];omega
  have rate:Squares p (tale (D f.prev).dine) α:=by
    have h:=(pages f.prev).1
    have eq:clock A Ñ s f.prev=α:=by
      change relativeC L Ñ N (age s f.prev) f.offset=relativeC L Ñ N (m+1) (N-(m+1))
      rw [AGE,DATE]
    exact eq ▸ h
  have unit:constantCoeff α=1:=angularC simple ratio (by omega)
  obtain ⟨book,actual⟩:=WilsonIndependentSpoutPaidAddon.original C Z D f Y L (s f.volW) (inc f.volW) c e pos
  refine ⟨book,?_⟩
  intro x
  specialize actual x
  simp only at actual ⊢
  rw [field S F H H' Q Ñ V rate unit hi] at actual
  have folded:coeff e (Blue.flash (mix (tale (D f.prev).dine) V))=coeff e (Blue.flash (mix α V)):=by
    simp only [Blue.flash,coeff_mk,source rate unit V hi]
  simp only [map_sub] at actual ⊢
  rw [folded] at actual
  exact actual

end YM.Integration.WilsonIndependentSpoutClockedPrint
