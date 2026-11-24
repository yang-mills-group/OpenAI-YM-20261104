import YM.LocalLTE.Fan.Plates
/-! Local producer at the Φ granule. Keep support Z expansion only (m+1). Price n any Pastel. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Fan.Field
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6 ConnectedActivityE6.Blaze Blaze.March Captain Mask Raw Matter Frond Coat Vine
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Gate Scroll Vine Tablet Metric Poll Flux Shield Pond Raw
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
open Brush Foramen Pastel Bakers PhysicalNext.Repeat Greenbelt Blaze.Stained Gas Ursell FrameBox.Grove FrameBox Sienna
variable {v z r W w s t y η γ B a μ b C C' q X Y κ d: ℝ} {j n k m N M : ℕ} {Q: YM.ConnectedActivityE6.Target G P}{o: Target.Order G W}{R:Rep G f}{χ:Chi}
-- θ on support P, reconstruct rep post using explicit transport & bring back to unforced channel. corticostencils.
def realised (H:Cash W t μ L Q o a T R) {p:ℕ}(A:Slots p→Finset (Veil c f))(U:Tuple H.ThinP p)(m k:ℕ)(r:ℕ→ℕ)(χ:Chi)(z:ℕ) {b:Site c}(X:FrameBox.Grove b)(κ:ℝ)(h:2*(2*z)≤ c.val): Config G c→ℝ:=
     FrameBox.realise X z κ (colorP (Field.owner H A U m k r (Fold.trace b z h) χ))
-- Both rendezvous radius Z0 internal log, Z' real, angles. Filled for INPUT ancestry only.
lemma occupancy {P:Teller G}(L:Side) (D:Patch)(hd:D.Branches P.bind G){N I Z :ℝ→ℕ}{M v₀:ℝ→ℝ}
   (Q:YM.ConnectedActivityE6.Target G P)(W:ℝ)(o:Target.Order G W)(p m n k j l g:ℕ)(hk:1≤k)(hl:l<j)(hm:pie m+1≤j)(hR:Q.rate < Pastel.mini)(hv: Pastel.mini*(k:ℝ) ≤ chip (m+1)-10*slack)(hV: (v+1/2)*((pie m+1:ℕ):ℝ) < 10*slack)(hW: -(1/2:ℝ) < v)(h:v<vow)(hη:γ<0)
    (h₀:max ((1/2:ℝ)*j+(γ+v)*j) (chip (m+1)-9*slack)+(v+(1/2-γ))*(l:ℝ) < chip (m+1)-7*slack)
    (hκ:Reliable G κ d)(hi:Rate G L 0 fun t=>(I t:ℝ))(hN:Rate G L 0 fun t=>(N t:ℝ))(hM:Rate G L 0 M)(hZ:Rate G L 0 fun t=>(Z t:ℝ))(hp:Rate G L (1/2) fun t=> (v₀ t)⁻¹): ∀ᶠ t in atTop, let β:=betaF G t L;
   ∀ (c f:Side)(S:StepData c f)(T:Tube G S), S.patch=D→ Stamp T→∀ (R:Rep G f) (μ σ:ℝ) (H:Cash W t μ L Q o σ T R)(U:Tuple H.ThinP p)(A:Slots p→ Finset (Veil c f)), (∀ i,(U i).val=arm (A i) ∧ Ac.Spark H.supportP (U i).val ∧ troupe T R Q.halo (radiusB t) (U i).val ∧ (A i).card≤n ∧ ((Field.pin (A i) H).card:ℝ)≤ M t)→
    ∀ (χ:Chi)(C d₀ V A' c' Y' B' q:ℝ)(k':ℕ)(K:Captain H j C d₀ (v₀ t) V A' c' Y' B' q k' χ), ∀ (r:ℕ→ℕ)(φ:ℕ→ℝ), let P := fisc (c:=c) R β φ;
    (∃ i k,Sum.inl k∈A i) → (∀ j i,i∈A j→ Breed R r φ β κ (N t) (I t) m i ∧ 0≤P i ∧ P i≤1) → ∀ B:BudgetPoint,B.threshold=Pressure.temp t → B.order=l→ B.power=g →∀ (b:Site c) (x y:ℕ), Captain.reachability (H:=H) ⟨p,U⟩ ⊆ neighbors x b → x+1≤y → y≤ Z t → 2*y<c.val→∀ (h:2*(2*x)≤c.val)(X:FrameBox.Grove b),
     let B₀:= |speedΛ H U| *Field.stock A P+K.design ⟨p,U⟩
     B.supBounds b (neighbors y b) ((fun z=>stream H χ z ⟨p,U⟩)-realised H A U m k r χ x X κ h) (B₀*β^(chip (m+1)-6*slack)):=by
   obtain ⟨a,hp₀,hp₂⟩:= exists_between hW; have hv':v<0:=by unfold vow at h; linarith
   let p' := chip (m+1)-7*slack
   obtain ⟨E,hE,HU⟩:= FrameBox.minted G L hZ hκ hp₂ hv' hp₀ (hp₂.trans h) l g
   filter_upwards [Delay.shift_pos G L, HU,(hE.mul (Rate.power (G:=G) (L:=L) (a:=p'))) (chip (m+1)-6*slack) (by unfold p' slack; linarith), Field.polarPrice L D hd Q W o p m n k j l hk hl hm hR hv hV hW (by unfold vow at h; linarith) hη h₀ hκ hi hN hM hp] with t hx hV hv hΓ β c f S T hS ht R μ σ H U A he χ C d₀ V A' c₀ Y' B' q k' K r φ L' hr h B hX hY hG b z x hh hP hV' hT ha X B₀
   let P : H.fragrances:=⟨p,U⟩; let Z':=neighbors z b
   let f₁ v:=stream H χ v P; let g:=Fold.trace b z ha (G:=G)
   let Q₀:= Field.owner H A U m k r g χ
   have hp' := (K.gloryBudget P B hX (hY.trans_le hl.le)).2.1
   have hΨ : B.Regular Z' f₁:= AnalyticBridge.CouplingShape.reg_extend hp' hh
   have hH:= H.laws.data
   have h₀ : 0≤ Field.stock A L':= prod_nonneg fun i _=> oil_nonneg A (fun j k hk=> h _ _ hk|>.2.1) _
   have hL: 0≤B₀:=add_nonneg (mul_nonneg (abs_nonneg _) h₀) (K.pvc _)
   let v':ℝ:= β^p'; let p₀:= B₀*v'
   have hp : ∀ u,f₁ (soloV u) = f₁ (soloV (g u)) := by
      intro u; rw [← Fold.rehearse]; exact (hΨ.sites _ _ (Fold.selfV b _ ha _ (by omega))).symm
   have hg : ‖g‖ ≤ 1:= ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun i=>by rw [one_mul]; exact Fold.invoice ..
   have hL': B.supBounds b (neighbors x b) _ (E t*p₀):= hV z x hV' hP B hG hY hX (hX.trans_le (hH.funds.length_eq ▸ hH.room.temperatures)) c b hT ha X _ Q₀ f₁ p₀ (mul_nonneg hL (Real.rpow_nonneg hx.le _)) hΨ (by
       intro x hx ht'; rw [Fold.rehearse] at ht'
       apply (hΓ c f -- f₁ shadow rename
         S T hS ht R μ σ H U A he χ C _ _ _ _ _ _ _ _ K r φ hr h B hX g hg x hx ht').shimmy
       exact Eventually.of_forall fun i=>congr_arg (fun z=> z-Cabana.actual Q₀ i) (hp i))
   have hy: E t*p₀ ≤ B₀*β^(chip (m+1)-6*slack):= by unfold p₀; rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans hv) hL
   exact ⟨(hL'.1.trans hy),fun y he l hl h => (hL'.2 _ he l hl h).trans hy⟩
end YM.LocalLTE.Fan.Field
