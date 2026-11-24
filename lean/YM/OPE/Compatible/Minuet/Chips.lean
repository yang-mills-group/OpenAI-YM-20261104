import YM.OPE.Compatible.Minuet.Latch
/-!
# reweighting and zero sum exactly, any b support
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Aroma
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03 Work.F03
open Bloch Laurent Progress.DirectedRecipe Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat Matter
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Gas Ursell Trees Animals Corona Daisy Leaf
open Planned.GuardedAtom.Guard
open AnalyticBridge.VerifiedReset
open Next.Rank.Thirst
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P':Teller G} {T: Tube G S} {R : Rep G f}
    {p : BudgetPoint} {m n: ℕ} {W a r t σ E Λ μ x κ C w ε D b B: ℝ}
variable {F:Forest S.ratio} {I J:Seats F}{X Y Z:Support f}{q:Support c}
variable (H:Primacy F I J Y X Z q R.p.B n) (P: S.patch.Branches S.kernel G)(hR:R.Lawful σ C Λ E w)(V:Config G c)(k:S.Choices)
variable (f':World F I G→ℝ)(hf:Envelope f'){A:ℝ}(hw:∀ w,‖f' w‖≤A)
variable (hD:WilsonStartup.Decent R.clip R.p)(hy:Geo.Width R.p R.clip σ)(hk:m ≤ R.p.B)(hN:∀ U:Config G f,naked S q n U B→ ordFrame S (halo 1 q) U ∧ ordBest S q U)(hb:4*B≤ R.p.threshold)(ha:a ≤ B)(hC:0≤B)
local notation "fL"=> allege I J R V m k a B H.nested f'
include H P hR hD hy hk hN hb ha hC hf hw
lemma chips {y:ℝ}(ht:0≤t)(hc:Sable R S X t (cinnamon R m I) y):
    S.push R.beta (fun U=>mellow R X U*(fL U*Real.exp (cinnamon R m I U))) V=0:=by
    let b:= fL; let w:=cinnamon R m I; let f₀ := mellow R X * (b * (Real.exp∘w))
    have hh:Paced R X S b (2*A):= allegation H P hR V k f' hf hw
    have hr :=(hc.expo ht); have hz := hr.present ht
    have hv:=stamps hR X; have hf₀:Envelope f₀ := hv.1.mul (hh.env.mul hz.1)
    have hp : Pedal S f₀:= fun k hv U=> congr_arg₂ (·*·) ((stamps hR X).2 k U) (congr_arg₂ (·*·) (hh.pedal k hv U) (hr.ped k hv U))
    change S.push R.beta f₀ V=0; rw [pedal_pack F R.beta f₀ P (hf₀.integrable _) hp V]
    let y p:= S.density R.beta (F.drape p) V * f₀ (F.drape p); have hk:=(S.isKernel P R.beta)
    have he(U: World F J G):= atReport I P hR V m k B f' hf hw U
    have hψ:Envelope y := by
       obtain ⟨z,hz⟩:=hk.bound; have hh:Envelope (fun p:F.Slice G=>S.density R.beta (F.drape p) V):=⟨Measurable.comp hk.meas (f:=fun p:F.Slice G=>(F.drape p,V)) (F.continuous_drape.measurable.prodMk measurable_const),z,fun u=> Real.norm_of_nonneg (hk.positive _ _)|>.trans_le (hz _ _)⟩
       exact hh.mul (Env.along hf₀ F.continuous_drape.measurable)
    let ξ(v:World F I G× Rim G I):=y (Wind I v.1 v.2)
    have ht:Envelope ξ:=Env.along hψ (threadT G I).symm.measurable
    change (∫ p,y p ∂F.order G)=_; rw [← (tapestry G I).symm.integral_comp' y]; change (∫ p,ξ p ∂_)=_
    rw [integral_prod_symm ξ (ht.integrable _)]; apply integral_eq_zero_of_ae; filter_upwards with x
    by_cases hu:∀ i: ↥(J\I), G.chord (x ⟨i.val,(mem_sdiff.mp i.property).2⟩)≤ a; swap
    · have hp(p:World F I G) : ξ (p,x)=0:=by
          have hs : ¬dazed H.nested a B (curveF F J (Wind I p x)):= mt ((faction H.nested a B p x).1) fun he=>hu he.2
          unfold ξ y f₀ b allege trawl; dsimp only; simp only [Pi.mul_apply, Function.comp_apply, chant_eq, if_neg hs]; ring
      simp_rw [hp,integral_zero]; rfl -- edit
    let A:=intoN I J x; let z:= F.drape (Wind I 1 x); let K:= S.density R.beta z V*mellow R X z
    let U p:= ballotY I R V m k B A p; let r:= report I J R V m k B f' A
    have hZ (p:World F I G): ξ (p,x)= K*(U p * (f' p -r)):=by
       rw [← (vows H P hR V k f' hD hy ‹m ≤ R.p.B› hN hb ha hC x hu p : _=K*_)]
       unfold ξ y f₀; simp only [Pi.mul_apply,Function.comp_apply]; unfold w b; ring
    simp_rw [hZ,integral_const_mul]; rw [(show (∫ p,U p*(f' p-r) ∂hail G I)=0 from (he A).2),mul_zero]; rfl
end YM.PhysicalNext.Repeat.Aroma
