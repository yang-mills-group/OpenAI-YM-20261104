import YM.RG01Estimate.RenderVac
/-! # Local Taylor ledger for normalized polynomial densities. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Receipt
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree Matrix
open Push Push.Uniform Push.SectorMeasure Presented PhysicalNext.Repeat
open PhysicalNext.Repeat.Lapis PhysicalNext.Repeat.Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums PhysicalNext.Repeat.Fare Sienna Conditioning Token Office Courtyard RealTaylor
open Laplace Laplace.Stellar Series
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge}
section type
variable {c f:Side}{S:StepData c f}(T:Tube G S)(F:Forest S.ratio)(B:BudgetPoint)
      (k:S.Choices)(r:Bid.Dir G c→AxisChart G F)(O:ChartRatio G)(t:ℝ)
local notation "X" => Positions (Uniform.Primary c G)
local notation "Y" => Poll.Body (Precision.Key F G)
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]

def orderMoments (w: Config G f→ℝ)(ℓ:Config G f→ E)(β:ℝ) (x:X):= normalized (S:=S) (G:=G) ℓ β w x

def mer (H:Y→ℝ×X→E): Policy X E:= vintage F T k r O H
def opt (j:ℕ)(v:Y→ℝ×X→ℝ)(H:Y→ℝ×X→E): Policy X E:=
     convolve (ContinuousLinearMap.lsmul ℝ ℝ) (Series.inverse (mer T F k r O v) j) (mer T F k r O H)

structure Article {E : Type} [NormedAddCommGroup E][NormedSpace ℝ E] (d D y β s v : ℝ) (X₀ : Positions (Uniform.Primary c G))
   (x : Config G f → E) (h : Y → ℝ×X→ E) (k j:ℕ) : Prop where
     meas : StronglyMeasurable x
     kept : GaugeInvariant x
     pos : 0≤ v
     existsJ : ∀ i, ‖x i‖ ≤ s*(Pane.virgin T B β).eval i
     onRoll : Roll h (closedBall 0 D) (ball 0 y) (breath G S.patch.L t) d j
     tall : Atlas h (ball 0 y) k j v
     reads (a) : a∈ closedBall (gStep β • X₀) (furl G S.patch.L t) →
           ∀ i:Y, ‖i‖≤D → let p:=field F r β a i
                         x p=(Pane.virgin T B β).eval p • h i (gStep β, (gStep β)⁻¹ • a)

structure Note (d D y β s v W w V n : ℝ)(x : Positions (Uniform.Primary c G)) (k₀ j r' A :ℕ) : Prop where
   place {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
       (f':Config G f→ E)(H:Y→ℝ×X→ E): Article T F B r t d D y β s v x f' H k₀ j →
              Hon (gStep β) r' A (mer T F k r O H) (organic F T r k O β f') W x
   charge (f':Config G f→ ℝ)(H:Y→ℝ×X→ℝ) : Article T F B r t d D y β s v x f' H k₀ j →
       (∀ z:Y,∀ x∈ball (0:X) y,H z (0,x)=1) →
            1/2 < organic F T r k O β f' x ∧ Hon (gStep β) r' A (Series.inverse (mer T F k r O H) r') (fun i=> (organic F T r k O β f' i)⁻¹) w x ∧
            Brush A ((gStep β)^r' * V) 1 (fun x=> vacuumS (S:=S) β f' x-report F T k r O β H r' x) x
   joint {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
        (Z:Config G f → E)(XQ:Y → ℝ × X→ E)(ℓ:Config G f→ ℝ)(H:Y→ℝ × X→ℝ): Article T F B r t d D y β s v x Z XQ k₀ j→ Article T F B r t d D y β s v x ℓ H k₀ j→
      (∀ z:Y,∀ x∈ball (0:X) y,H z (0,x)=1) →
            Hon (gStep β) r' A (opt T F k r O r' H XQ) (orderMoments (S:=S) ℓ Z β) n x
end type
section expose
variable {q:Teller G}
lemma stellar_bills (j:ℕ)(G:Gauge)(L:Side)(f y:ℝ→ℝ)(hf:Cookie G L f)(hy:Cookie G L y) :
       Cookie G L (fun i=> axial (j+2) (f i) (y i)+luxury j (f i) (y i)) := by
    have hk(j):Cookie G L (fun i=>axial j (f i) (y i)):= (hy.expense j).lump (((((Laplace.Cookie.const 1).joins hf).joins ((Laplace.Cookie.const 1).joins hf))).lump hf j) j
    exact (hk _).joins ((hk j).joins ((hy.expense j).lump hf j))

variable {α u σ σ' C C' : ℝ}{i j n:ℕ}{K: KernelChoices}(P:Patch)(c c':Clip)(Q:ConnectedActivityE6.Target G q)
   (o:Target.Order G α)(A:Before G σ C P.J K (n+3))(ζ : BareRates.pre G σ' C' (n+3))(v : FiberFee Q.table ((n+3)+1))
local notation "Vq" => A.tables c P
include v ζ in
lemma wide_pay (f:ℝ→ℝ)(hA:2 ≤ n)(hu:0 < u)(hf:Bolt G P.L f) : ∃ d:ℝ, ∃ Z:ℝ→ℝ, 0<d ∧ Cookie G P.L Z ∧
      ∀ (r j i:ℕ) (s Y a e:ℝ→ℝ)(m:ℝ), r+j ≤ n→ 0<r→ Cookie G P.L a→ Cookie G P.L e→ Cookie G P.L Y→Rate G P.L m s→
           ∃ W w p n':ℝ→ℝ, Cookie G P.L W ∧ Cookie G P.L w ∧ Cookie G P.L p ∧ Cookie G P.L n' ∧ ∀ᶠ t in atTop,
      ∀ c₀ c₁:Side,∀ (S:StepData c₀ c₁)(T:Tube G S)(F:Forest S.ratio)(h:S.patch=P)(hm:S.kernel=K), Quilt T F (f t) →
       T.high=c→ T.low=c' → T.up.Bounds c σ C (ConnectedActivityE6.loopBill G P.L t) → ∀ Λ', T.down.Bounds c' σ' C' Λ' →
       ∀ ρ:Bid.Dir G c₀→AxisChart G F, (warm A h hm).Service F T.high T.up ρ → ClassicalMatch F T.high T.low T.up T.down ρ → ∀ (k:S.Choices) (hC: Coat T F),hC.x=t → hC.width=o.K → hC.manifest →
       ∀ (x:Positions (Uniform.Primary c₀ G))(B B':BudgetPoint)(β m':ℝ), B'.threshold=Pressure.temp t → Cash α t u P.L Q o m' T (Pane.virgin T B β) →
        0 ≤ s t → 1 ≤ Y t→ ‖x‖+1< Y t→ hC.V= represent (tint G _ (gStep β • x)) → flags (Pressure.temp t) hC.V=∅ →
       Note T F B k ρ Q.table t (a t) (wick G P.L d t) (Y t) β (s t) (e t) (W t) (w t) (p t) (n' t) x i n r j ∧
       ∃ ε:ℝ, ∀ z ∈ closedBall (gStep β • x) (furl G S.patch.L t), (gStep β)⁻¹ • z ∈ ball 0 (Y t) ∧ Interior F T Q.table k ρ B β (wick G P.L d t) z (eaves G P.L t) (Z t) ε n := by
   let L:=P.L; let b:= Vq
   obtain ⟨d,hd,h⟩:= Courtyard.pass Q o P A c' c f hf v ζ u hu (by omega)
   let Z t:= pam n Q.table c P A (f t) (f t) v (ConnectedActivityE6.loopBill G L t); let D:= wick G L d
   obtain ⟨-,a₀,v',ha',hv,H⟩:= posts P.L P Q.table c A v hf
   have hZ: Cookie G P.L Z:= (Cookie.bolt ha'|>.joins ((Cookie.bolt hv).pays Cookie.mast)).copy (Eventually.of_forall H)
   refine ⟨d,Z,hd,hZ,fun r j i s Y a e m hn hr ha he hY hs=>?_⟩
   let k x:= f x * (Fintype.card Axis:ℝ)
   let C₀:= if h:0<b.gap then b.gap else 1
   have hc₀:0<C₀:= by unfold C₀; split_ifs <;> first|assumption| exact zero_lt_one
   obtain ⟨W,hW,hD⟩:= read_shape G P.L K j n i r (by omega) (by omega) m C₀ d (C₀/2)⁻¹ hc₀ hd (inv_pos.mpr (half_pos hc₀)) s Y Z k a f e hs hY hZ hf (hf.uses.mul_right _) he ha
   obtain ⟨C₁,C₂,hk,hq,hΛ⟩:= Series.normalizes G P.L r j W hr hW
   let Ξ t:= axial (n+2) (Z t) (Y t)+luxury n (Z t) (Y t); let Ξ₁ i:=Ξ i+C₁ i
   refine ⟨W,C₂,Ξ₁,(fun t=> addition j r 1 (C₂ t) (W t)),hW,hq,(stellar_bills n G P.L Z Y hZ hY).joins hk, paid_mul j r hq hW,?_⟩
   filter_upwards [h,hD,hΛ,funding n d hZ.uses hY.uses,(Work.E09.betaF_growth G L).eventually_ge_atTop 4] with t ht ht' hm ht₀ htB c₀ c₁ S T F hP hK H hc hc' hV Λ hL ρ hS hρ l X hX he' hΦ x B B' β m' hB hG hN hY hx hr' hh
   let f:= breath G P.L t; let g:=gStep β; let o':= eaves G P.L t
   let w:= Pane.virgin T B β
   have hZ₀ : 0<betaF G t L:=by linarith
   have hi:S.patch.L=P.L:=congr_arg (fun p: Patch=> p.L) hP
   have hJ:= hG.laws.intake
   have h₀:0<β:= hJ.positive; have hg:0<g:=(Fare.gS β h₀).1
   have hZ₁ : betaF G t P.L/2 ≤ β := hi ▸ hJ.window.1
   obtain ⟨h0,h1,h2,h3,h4⟩:= ht₀
   have h : g < f:= h4 β hZ₁; have hz : ∀ y:Positions (Uniform.Primary c₀ G),‖y‖<Y t→‖g • y‖ < o':= fun y hy=> by
      rw [norm_smul,Real.norm_of_nonneg hg.le]; exact (mul_lt_mul_of_pos_left hy hg).trans_le ((mul_le_mul_of_nonneg_right h.le (zero_le_one.trans hY)).trans h1)
   have hx' := ht _ _ S T F hP hK H hc hc' hV Λ hL ρ hS hρ l X hX he' hΦ B B' m' β hG hB hh (g • x) hr' (hz x (by linarith only [hx]))
   let M:= Lapis.gram F T.up T.high ρ l
   have h' : b=(warm A hP hK).tables T.high S.patch:= by subst K; subst P; subst c; rfl
   have hp₀:(C₀)=((warm A hP hK).tables T.high S.patch).gap:= by
      have hv:= hx'.1; unfold C₀; rw [h',dif_pos hv]
   have hf:Sienna.furl G L t ≤ g:= (Laplace.roots t β htB h₀ (show β≤2*betaF G t P.L from hi ▸ hJ.window.2)).1
   let ζ:=ball (0:Positions (Uniform.Primary c₀ G)) (Y t)
   let O:=closedBall (g • x) (furl G L t)
   let ε:= Real.exp (-(C₀*D t^2/4)/2); have ho:g • x∈ O:=mem_closedBall_self (Real.rpow_nonneg hZ₀.le _)
   have hXi y (hy:y∈ O): g⁻¹ • y ∈ ζ ∧ Interior F T Q.table l ρ B β (D t) y o' (Z t) ε n:= by
       have hr : ‖g⁻¹ • y - x‖ ≤ 1:= by
          rw [show g⁻¹ • y-x=g⁻¹ • (y-g • x) from by rw [smul_sub,inv_smul_smul₀ hg.ne'],norm_smul,Real.norm_of_nonneg (inv_pos.mpr hg).le]
          apply (inv_mul_le_iff₀ hg).mpr; rw [mul_one]; exact (mem_closedBall_iff_norm.mp hy).trans hf
       have hZ : ‖g⁻¹ • y‖< Y t:= (norm_le_norm_add_norm_sub' _ _).trans_lt ((add_le_add_right hr ‖x‖).trans_lt hx)
       have hu' : ‖y‖< o':= smul_inv_smul₀ hg.ne' y ▸ hz _ hZ
       unfold ε Z D L; rw [hp₀]; exact ⟨mem_ball_zero_iff.mpr hZ,hx'.2.2 y hu' (mem_closedBall_iff_norm.mp hy)⟩
   have hJ' := hXi _ ho |>.2
   have hρ' := wakes F l T.up T.high ρ σ C (ConnectedActivityE6.loopBill G P.L t) (warm A hP hK) H.large (hc ▸ hV) hS 0 ((show ‖(0:Positions (Uniform.Primary c₀ G))‖<o' by rw [norm_zero]; exact hJ'.calcJ.pos).trans_le hx'.2.1)
   have hj : (Fintype.card (Bond c₀):ℝ) ≤ k t:= by rw [Fintype.card_prod]; push_cast; exact mul_le_mul_of_nonneg_right H.primary (by positivity)
   have hxv:x∈ ζ:= mem_ball_zero_iff.mpr (by linarith only [hx])
   have hP {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E](f:Config G c₁→ E)(g:Poll.Body (Precision.Key F G) → ℝ × Positions (Uniform.Primary c₀ G) → E) (hp:Article T F B ρ t (a t) (D t) (Y t) β (s t) (e t) x f g i n):
       Hon (gStep β) r j (mer T F l ρ Q.table g) (organic F T ρ l Q.table β f) (W t) x:= by
       obtain ⟨hf,hk,hx,he,hl,hS,hK'⟩:= hp
       rw [hi] at hl hK'
       have hu y:= hρ'.2.2.1 y; rw [← hp₀] at hu
       obtain ⟨hx,hb'⟩:= ht' _ _ S F T B q β Q.table l ρ hi hK hj (countsK _ _ H.overall) H.one hY hN hJ (hρ'.1.inv) hu _ hxv hXi _ f g hf hk he hK' hl hS hx
       exact Laplace.dignified F T l ρ Q.table g β hx hb' (by omega) h₀
   have hk f H' (h':Article T F B ρ t (a t) (D t) (Y t) β (s t) (e t) x f H' i n) (hT:∀ z,∀ x∈ζ,H' z (0,x)=1):= hm _ (organic F T ρ l Q.table β f) (mer T F l ρ Q.table H') x β hZ₁ (hP _ _ h')
       (show mer T F l ρ Q.table H' 0=ᶠ[_] 1 from Filter.Eventually.mono (show ∀ᶠ y in 𝓝 x,y∈ζ from isOpen_ball.mem_nhds hxv) (fun y hy=> Laplace.still_unit _ _ _ _ _ _ _ (fun z=> hT z y hy))) -- formatting
   refine ⟨⟨fun _ _ h=> hP _ _ h,fun f H' hv hν=>?_,fun Z V P' Z' h hv hr=> ?_⟩,ε,?_⟩
   · obtain ⟨hX,hM,h0',hm,hy⟩:= hk _ _ hv hν
     have hr:= Stellar.back _ _ _ _ _ hJ'.calcJ Q.table_exists h1 hY h0 β h₀ x (show (g,x)∈ corridor _ ζ from ⟨mem_ball_zero_iff.mpr (by rw [Real.norm_of_nonneg hg.le]; exact h),hxv⟩) (show j+r≤n by omega)
     exact ⟨hX,hy, unscan F T l ρ Q.table β H' f Q.table_exists h₀ x hm ((by norm_num : (0:ℝ)<1/2).trans hX) ((hP _ _ hv).bear (by rw [abs_of_pos hg]; exact hM)).smooth.continuousAt hr⟩
   · obtain ⟨-,hz,_,_,h₀'⟩:=hk _ _ hv hr
     exact marked_relative F T l ρ Q.table Z V β Z' P' Q.table_exists h₀ hz h₀' (hP Z V h) -- order
   rw [hi]; exact hXi
include v ζ in
lemma horizon_pay (r : ℕ) (s Y a e f:ℝ→ℝ)(m:ℝ)(hn:r+j ≤ n)(hr:0<r)(hA:2≤n)(hu:0<u)
   (hf:Bolt G P.L f)(ha:Cookie G P.L a)(he:Cookie G P.L e)(hY:Cookie G P.L Y)(hs:Rate G P.L m s) :
   ∃ d:ℝ, ∃ W w p n':ℝ→ℝ, 0<d ∧ Cookie G P.L W ∧ Cookie G P.L w ∧ Cookie G P.L p ∧ Cookie G P.L n' ∧ ∀ᶠ t in atTop,
      ∀ c₀ c₁:Side,∀ (S:StepData c₀ c₁)(T:Tube G S)(F:Forest S.ratio)(h:S.patch=P)(hm:S.kernel=K), Quilt T F (f t) →
       T.high=c→ T.low=c' → T.up.Bounds c σ C (ConnectedActivityE6.loopBill G P.L t) → ∀ Λ', T.down.Bounds c' σ' C' Λ' →
       ∀ ρ:Bid.Dir G c₀→AxisChart G F, (warm A h hm).Service F T.high T.up ρ → ClassicalMatch F T.high T.low T.up T.down ρ → ∀ (k:S.Choices) (hC: Coat T F),hC.x=t → hC.width=o.K → hC.manifest →
       ∀ (x:Positions (Uniform.Primary c₀ G))(B B':BudgetPoint)(β m':ℝ), B'.threshold=Pressure.temp t → Cash α t u P.L Q o m' T (Pane.virgin T B β) →
        0 ≤ s t → 1 ≤ Y t→ ‖x‖+1< Y t→ hC.V= represent (tint G _ (gStep β • x)) → flags (Pressure.temp t) hC.V=∅ →
       Note T F B k ρ Q.table t (a t) (wick G P.L d t) (Y t) β (s t) (e t) (W t) (w t) (p t) (n' t) x i n r j := by
   obtain ⟨d,Z,hd,hZ,h⟩:= wide_pay (u:=u) P c c' Q o A ζ v f hA hu hf
   obtain ⟨W,w,p,m',hW,hw,hp,hm,h⟩:= h r j i s Y a e m hn hr ha he hY hs
   refine ⟨d,W,w,p,m',hd,hW,hw,hp,hm,?_⟩
   filter_upwards [h] with t ht c f S T F h hp' hr hS hT hk v hv ρ hc hL k V hQ hX hZ x B B' β y hs' hq hR hR' hη hG he
   exact (ht c f S T F h hp' hr hS hT hk v hv ρ hc hL k V hQ hX hZ x B B' β y hs' hq hR hR' hη hG he).1
end expose
end YM.RG01Estimate.Receipt
