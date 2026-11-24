import YM.OPE.Compatible.Lintel.Whet
/-! # VIBE away (cofinal ordinary periods enough). -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Work.F05
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J Y Z:Type}{G:Gauge}{n m c f:Side}{S:StepData c f}{p q:Clip}{R T:PathData G} {P:Patch}{K:KernelChoices}{V:ChartRatio G} {i j t r:ℕ} {s s' u α T₁ T₂ b b' d U ℓ:ℝ}
namespace Script
open Page Virgin
variable {w: Boxes G P K}
def TrainTell (w:Boxes G P K)(p q:Clip)(R T: PathData G)(α:ℝ)(V:ChartRatio G):Prop:= ∃ c:ℕ→Side, Tendsto (fun i=> (c i).val) atTop atTop∧∃ Z Y W:ℝ,0<Y∧∀ i:ℕ,let S: StepData (c i) (c i*P.L):=⟨P,K,rfl⟩; let hr:= P.odd_side; let F:=forest S.ratio hr
      ∃ B A g,licensed S hr w p R A B g ∧ ClassicalMatch F p q R T g∧ FiniteBound F R T p q α V g Z Y W
def TEX (w:Boxes G P K)(p q:Clip)(R T:PathData G)(α:ℝ)(V:ChartRatio G):Prop:= inkV T q 3=stitch (w.T3 R p)∧ inkV T q 4=stitch (w.T4 R p)∧ leafV T 2+α • inkV T q 2=stitch (w.talo R p V)
lemma prime_weave (hq: LocalRatio V)(h:TrainTell w p q R T α V)(hp:R.Bounds p s u b)(he:T.Bounds q s' b' d): TEX w p q R T α V:=by
    obtain ⟨m,hm,Z,Y,W,hy,H⟩:=h; let S(i:ℕ): StepData (m i) (m i*P.L):=⟨P,K,rfl⟩; let t(i): (S i).Choices:=Classical.arbitrary _
    have ht:=folk_whole (p:=w.talo R p V) (folkT w.rocket2 (w.folk_crown hp)) -- `(V:=` not argument
    have hh:=folk_vol w p R hp 3; have hz (r k):= inkSongs T q 1 r k he; refine ⟨away (q:=stitch (w.T3 R p)) (sootS (hz 3 0).2.1.choose_spec) (folk_whole (folkst _ hh)) (hz 3 0).1 (stampV _ (folk_whole hh)) m hm (Eventually.of_forall fun i v=>?_),away (q:=stitch (w.T4 R p)) (sootS (hz 4 0).2.1.choose_spec) (folk_whole (folkst _ (folkT w.rocket2 (w.folk_om hp)))) (hz 4 0).1 (stampV _ (folk_whole (folkT w.rocket2 (w.folk_om hp)))) m hm (Eventually.of_forall fun i v=>?_),?_⟩
    · obtain ⟨A,L,g,ha,hM,hV⟩:=H i; rw [regaled _ (folk_whole hh)]; exact lesson3 (S i) P.odd_side w ha hp he hM (t i) v
    · obtain ⟨A,L,g,ha,hM,hV⟩:=H i; rw [regaled (w.T4 R p) (folk_whole (folkT w.rocket2 (w.folk_om hp)))]; exact lesson4 (S i) P.odd_side w ha hp he hM (t i) v
    let A:= expose (draftY q T α); let B:= stitch (w.talo R p V); rw [add_comm, ← rescaleInk]; change A=B; obtain ⟨hz1,hz2,hz3⟩:=leafSongs T q 1 2 0 he; have h1:A=α • inkV T q 2+ leafV T 2:=rescaleInk ..; have hh :A.Idem:= h1.symm ▸ (idemAdd _ _ (idemScale _ _ (hz 2 0).1) hz1 (sootS (Sack.scale_line (hz 2 0).2.1.choose_spec α)) (sootS hz2.choose_spec)); have hB : B.Idem:=stampV _ ht
    have hd:Summable A:= h1.symm ▸ (((sootS (hz 2 0).2.1.choose_spec).const_smul α).add (sootS hz2.choose_spec) : Summable (α • inkV T q 2+ leafV T 2)); have hK:Summable B:=folk_whole (folkst _ (folkT w.rocket2 (w.folk_crown hp)))
    ext1 x; by_cases hx:primary x=0; swap; · rw [show A x=0 from not_ne_iff.mp fun h=>hx (hh.1 x h), show B x=0 from not_ne_iff.mp fun h=>hx (hB.1 _ h)]
    let f (i:ℕ):= library (m i) A (hand x (m i)); let g (i:ℕ):= library (m i) B (hand x (m i)); have hu : Tendsto f atTop (𝓝 (A x)) := (lands A hd x m hm).congr (fun i=> (centerSync A hh.1 hx (m i)).symm)
    have hv : Tendsto g atTop (𝓝 (B x)):= (lands B hK x m hm).congr (fun i=> (centerSync B hB.1 hx (m i)).symm)
    obtain ⟨C,hc,hF⟩:= w.rapid (V:=V) hp 1; simp only [pow_one] at hF; apply sub_eq_zero.mp; apply tendsto_nhds_unique (hu.sub hv); apply tendsto_zero_iff_norm_tendsto_zero.mpr
    let n (i:ℕ):ℝ:= (m i).val; have hn: Tendsto n atTop atTop:= tendsto_natCast_atTop_atTop.comp hm
    refine squeeze_zero' (Eventually.of_forall fun i=>norm_nonneg _) (Eventually.of_forall (p:=fun i=> ‖f i-g i‖ ≤ (12*C/n i)+(n i)^4*Z*W*Real.exp (-Y*(n i))) (fun i=>?_)) ?_
    · obtain ⟨a,l,g',hL,hC,hG⟩:= H i; let hX:= hand x (m i); rw [show f i-g i=library (m i) A ![hX 0,hX 1]-library (m i) B ![hX 0,hX 1] from ?_,norm_sub_rev]; exact tug (S i) _ w (t i) hL hp he hq hG hc hF _ _ -- give j k
      change library (m i) A hX-library (m i) B hX=_; rw [show hX=![hX 0,hX 1] from funext fun i=>by fin_cases i<;>rfl]; rfl
    have hf:= (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 4).comp (hn.const_mul_atTop hy); let a:=12*C; let c' := Z*W / Y^4
    have ht' : Tendsto (fun i:ℕ=> n i ^4 * Z *W *Real.exp (-Y*(n i))) atTop (𝓝 0):=by
        have ha:= hf.mul_const c'; rw [zero_mul] at ha; refine ha.congr fun i=>?_ ; change (Y*n i)^4*Real.exp (-(Y*n i))*_=_; unfold c'; rw [neg_mul]; field_simp
    rw [← add_zero (0:ℝ)]; exact Tendsto.add (tendsto_const_nhds.div_atTop hn) ht'
end Script
end YM.OPE.Flume
