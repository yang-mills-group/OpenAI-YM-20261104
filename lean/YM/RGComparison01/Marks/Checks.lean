import YM.RGComparison01.Marks.Foreman
import YM.RGComparison01.Ports
/-!
 # Stencil charge for weighted ANALYTIC and forced branches

 After building scales with the ambient Family. Gives sharp cut and high
 arity. Keep all tickets including even same-log-root probes in the hits;
 no cancellation of rough E costs. Excludes no pollen in claiming identity.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Pledge
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter Mixed Reserves
open PhysicalNext PhysicalNext.Repeat Packets Art Silica Poll Pond Shield Eider Gas Ursell Trees Height Sail
open PhysicalNext.Repeat.Lotus Team Merge
open AnalyticBridge VerifiedReset Collection Quotes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge} {ι : Type} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : RG.Rep G f}
    {n : ℕ} {W a r σ Λ μ s κ w c' C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
    {H : Cash W s μ L Q o C T R} {d C' A B e δ t D D' v K :ℝ} {j k ℓ:ℕ} {χ:Chi} {Ω : Utopia H j v d r C' χ}
    {Ψ : ℕ → Prop} {x:ℕ→ℝ}
namespace Checks
open Baked Palette Pillow Resin Foreman March Opacity
variable (M:ι→Leaf R)(H:Cash W s μ L Q o C T R)(Ω:ℕ→Prop) (ρ:ι→ℝ)
local notation "CA" => Cake M H
local notation "CL" => Cl M H
local notation "xp" => (radiusB s)
local notation "Zt" => (Q.mark L μ s)
-- purchase quota
structure Cellar (Q:ConnectedActivityE6.Target G P)(χ:Chi) (W:ℝ)(L:Side)(M₁ : Patch)(o:Target.Order G W) (j k k' n : ℕ) (μ a δ :ℝ) (b u y Y U:ℝ → ℝ) (t:ℝ) : Prop where
   sizes : Height.grow G L t^k ≤ zephyr Q L t^k'
   long : Height.grow G L t^k ≤ Real.exp (Q.ε*radiusB t)
   covers : incomingE G L t ≤ min 1 (b t)
   life : 1 ≤ Height.grow G L t
   buys : ∀ (c f : Side) (S:StepData c f)(T:Tube G S), S.patch=M₁ → Stamp T → ∀ R C (H:Cash W t μ L Q o C T R),
       ((∀ (ι:Type)[Fintype ι] (M:ι→Leaf R) (g:ι→ℝ), Bench M g (b t) → Ringlet H M g a δ (u t) (16*u t)) ∧
       ∃ (j':ℕ) (v r d C' E B h w d' x:ℝ) (Ξ : Utopia H j v d r C' χ), Knot Ξ E B h w d' x j' ∧
         ∀ (ι:Type) [Fintype ι] (M:ι→Leaf R) (g:ι→ℝ), Bench M g (b t) → ∀ (D:ℕ→Prop) (e δ : ℝ),
           (Tithe.portion R.activities D).EBound R.p e → e ≤ incomingE G L t → 1 ≤ δ → δ*e ≤ b t →
           ∃ x:ℕ→ℝ,Casing R x D ∧ Ac.Hit (origins M H) (radiusB t)
          (fun p=> Baked.weight M (fun v=> sheen M v D δ (zephyr Q L t) (Height.grow G L t^k)) p * RegDebt M g p Ξ j' n B (maskRaise Ξ D x E)) a (y t))
   pole : 1 ≤ zephyr Q L t
   crucial : 0 < b t
   shores : U t= (b t)⁻¹
   spelled : y t * (b t)⁻¹ = Y t

-- maybe B visits not enforced, remove
lemma bought (G : Gauge) (P:Teller G)(Q:ConnectedActivityE6.Target G P)(a δ:ℝ)(ha:0≤a)(he:0<δ)(hh:a+δ+δ ≤ Q.exp) : ∃ l:ℕ,∀ (L:Side),l ≤ L.val → ∀ (M₁:RG.Patch), M₁.Branches P.bind G → ∀ (χ:Chi)(μ W:ℝ),0<μ → 0<W → ∀ (o:Target.Order G W) (p k n:ℕ), ∃ (b u y Y U:ℝ → ℝ) (k':ℕ), Geo G L b ∧ Geo G L u ∧ Geo G L y ∧ Geo G L Y ∧ Geo G L U ∧ ∀ᶠ t in atTop,
   Cellar Q χ W L M₁ o p k k' n μ a δ b u y Y U t := by
   obtain ⟨i,hS⟩:= Team.cloak_team P Q; obtain ⟨n,hp⟩:= Pledge.payments P Q; refine ⟨i+n,fun L hl M₁ hM χ μ W hθ hW o j k n'=>?_⟩
   obtain ⟨A,b,hA⟩:= Eider.weave G; obtain ⟨Z,hZ,hq⟩:= March.oar G j
   let ξ x := 2*Pressure.fiery G x L; let u x:= ((j:ℝ)+1)*Z*(ξ x)
   have hv:Fine G L u:= Fine.grind_left (Geo.fixed _) (Fine.grind_left (Geo.fixed _) Fine.flame)
   have hx:∀ᶠ x in atTop,0<ξ x:= ((Work.E09.betaF_growth G L).eventually_gt_atTop 0).mono fun x h=> mul_pos (by norm_num) (Work.E09.temp_pos h)
   obtain ⟨e,C,q,r,t,P',h₁,hr,hg,hX⟩:= hS L (by omega) M₁ hM j χ W hW μ hθ o A b hA u k hv (hx.mono fun x hh=>by unfold u; positivity)
   obtain ⟨k',hF'⟩:= booked Q L k
   have hh0 : ∀ᶠ t in atTop, Height.grow G L t^k ≤ Real.exp (Q.ε*radiusB t):= by
     have hz: Rate G L (3/8) (Height.grow G L):= Rate.power
     have ht': Rate G L (-(((3/8:ℝ)*k)+1)) (fun x=> Real.exp (-Q.ε*radiusB x)):= by
       refine Rate.compare (Rate.cutoff (δ:=Q.ε) Q.usable) ?_
       filter_upwards with x; simp only [abs_of_pos (Real.exp_pos _)]
       apply Real.exp_monotone; rw [neg_mul,neg_mul]; apply neg_le_neg; apply mul_le_mul_of_nonneg_left _ Q.usable.le
       exact_mod_cast Nat.div_le_self ..
     filter_upwards [((hz.pow k).mul ht').below (by ring_nf; norm_num) 1 zero_lt_one] with x hx
     apply le_of_mul_le_mul_right _ (Real.exp_pos (-Q.ε*radiusB x)); apply le_trans ((le_abs_self _).trans hx); rw [neg_mul,← Real.exp_add,add_neg_cancel,Real.exp_zero]
   obtain ⟨vB,w,Pp,U,hvB,hw,hP,hU,hC⟩:= capital Q L hg hr (μ:=μ) hθ j P' (e:=e) (δ:=δ)
   let y t:= collars G δ t j n' * (Pp t*(1-1/2:ℝ)⁻¹); have hy:Geo G L y:= collar_price.times (hP.times (Geo.fixed _)); have hh' := hU.rate
   have hK:= ((incomingE_rate G L).mul hU.rate).below (by norm_num) 1 zero_lt_one
   refine ⟨vB,Pp,y,(fun t=>y t*U t),U,k',hvB,hP,hy,(hy.times hU),hU,?_⟩
   filter_upwards [hh0,hK, (incomingE_rate G L).below (by norm_num) 1 zero_lt_one,hx,hp L (by omega),hF',hC,hX,(Work.E09.betaF_growth G L).eventually_ge_atTop 1] with
      s h₀ hK hJ hx hp hΛ hC hX h'
   have hi:= hC.2.sits; have hw : 1≤ zephyr Q L s:= Real.one_le_rpow h' (width_power Q L).le
   have hf:1 ≤ Height.grow G L s:= Real.one_le_rpow h' (by norm_num)
   have he : incomingE G L s ≤ min 1 (vB s):= le_min ((le_abs_self _).trans hJ) (by
     rw [hC.1] at hK; have hx := (le_abs_self _).trans hK; simpa only [one_mul] using (mul_inv_le_iff₀ hi).1 hx)
   refine ⟨hΛ,h₀,he,hf,fun c f S T hS ht R C' H=>?_,hw,hi,hC.1,by rw [← hC.1]⟩
   obtain ⟨X,hJ,hF⟩:=hX _ _ _ T hS ht R _ H
   have hP:=hp c f S T R H.laws.data.funds.length_eq H.laws.intake
   have hX:Knot X e (t s) A b (ξ s) (Z*ξ s) P':= ⟨hF,(by have he:= H.laws.data.room.temperatures; rw [H.laws.data.funds.length_eq] at he; exact he),(by unfold u; positivity),(by positivity),⟨fun c=> hq c _ hx.le⟩,(by unfold u; nlinarith [mul_nonneg hZ.le hx.le])⟩
   exact ⟨fun _ _ M g hz=> tracks M g hz hP hw hC.2 ha (by assumption) hh hF,P',u s,r s,q s,C,e,t s,A,b,ξ s,Z*ξ s,X,hX,fun _ _ M g hz D e' δ' ht hx hδ ht'=> enrollment M g hz hP hw hC.2 ha (by assumption) hh X hJ hX hf ht (hx.trans ((he.trans (min_le_left ..)))) (one_le_pow₀ hf) hδ ht' n'⟩
end Checks
end YM.RGComparison01.Pledge
