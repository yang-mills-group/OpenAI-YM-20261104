import YM.LocalLTE.Fan.Season
/-! Laurent scout finite powers at Pastel order s. β tower projection without altering occupancy. -/
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
open Brush Foramen Pastel Bakers PhysicalNext.Repeat Greenbelt Blaze.Stained Gas Ursell
variable {v z r W w s t y η γ B a μ b C C' q X Y κ d : ℝ} {j n k m N M : ℕ} {Q: YM.ConnectedActivityE6.Target G P}{o: Target.Order G W}{R:Rep G f}{χ:Chi}
-- include manifold checks and Kost relation. lonely epsilon. Call at any ℓ finances, Hats. Uniform many labels paid later using Halos.
lemma pilot {P:Teller G}(L:Side) (D:Patch)(hd:D.Branches P.bind G){N I:ℝ→ℕ}{M:ℝ→ℝ}(Q:YM.ConnectedActivityE6.Target G P)(W:ℝ)(o:Target.Order G W)(p m n k:ℕ)(hk:1≤k) (hR:Q.rate < Pastel.mini) (hv: mini*(k:ℝ) ≤ chip (m+1)-10*slack)(hV: (v+1/2)*((pie m+1:ℕ):ℝ) < 10*slack)(hW: -(1/2:ℝ) ≤ v)(h: v<0)(hκ:Reliable G κ d)(hi:Rate G L 0 fun t=>(I t:ℝ))(hN:Rate G L 0 fun t=>(N t:ℝ))(hM:Rate G L 0 M):
   ∀ᶠ t in atTop, let B:=betaF G t L; let w:= B^v
   ∀ (c f:Side)(S:StepData c f)(T:Tube G S), S.patch=D→ Stamp T→∀ (R:Rep G f) (μ σ:ℝ) (H:Cash W t μ L Q o σ T R)(U:Tuple H.ThinP p)(A:Slots p→ Finset (Veil c f)), (∀ i,(U i).val=arm (A i) ∧ Ac.Spark H.supportP (U i).val ∧ troupe T R Q.halo (radiusB t) (U i).val ∧ (A i).card≤n ∧ ((Field.pin (A i) H).card:ℝ)≤ M t)→
    ∀ (χ:Chi)(C d₀ v₀ V A' a Y' B' q:ℝ)(j k':ℕ),Captain H j C d₀ v₀ V A' a Y' B' q k' χ → ∀ (r:ℕ→ℕ)(φ:ℕ→ℝ), let Z := fisc (c:=c) R B φ;
    (∃ i k,Sum.inl k∈A i) → (∀ j i,i∈A j→ Breed R r φ B κ (N t) (I t) m i ∧ 0≤Z i ∧ Z i≤1) →
    ∀ u:Directions G c, let x:Disk G c:=(gStep R.beta,u)
    RG.flags (Pressure.temp t) (increment 1 u)=∅→ ‖x‖<w →
    ‖(∏ i, leaflet H χ (increment 1 u) (U i))-Field.forecast H A m k r χ x‖≤ Field.stock A Z *B^(chip (m+1)-9*slack):=by
   let p' x:= Inset.cone v (betaF G x L); have h₀:Rate G L v p':= Rate.power; let ξ:= chip (m+1)-10*slack; have hξ:ξ≤0:=by unfold ξ chip slack; exact (by push_cast; linarith [Nat.cast_nonneg (α:=ℝ) m])
   let B x:=betaF G x L; let Z x:=(B x)^ξ
   let n':= pie m + 1
   obtain ⟨Y,hY,HA⟩:= Bakers.passage L D hd Q W o n' m k n (by unfold n'; omega) hW h h₀ (by filter_upwards [Delay.shift_pos G L] with x hx using Real.rpow_nonneg hx.le _) hκ hi hN hM
   let q x:= leftOver p n k m (B x) (Z x); let PP x:= B x ^ (castRank n' m)* (((k:ℝ)^n)^(p+1)*hCost (|Y x|) p k n') * (p' x)^ n'; let g x:= q x+PP x
   have hZ' : Rate G L ξ Z:= Rate.power
   have hq:Rate G L ξ q := by
     let v x:= envelope (B x) (Z x) n k; let f x:= 1+v x+(k:ℝ)^n
     have hv : Rate G L ξ v:= (hZ'.add ((((Rate.power (a:=mini)).pow k).weaken hv).mul_left (n:ℝ))).mul_left _
     have hf : Rate G L 0 f:= ((Rate.const _).add (hv.weaken hξ)).add (Rate.const _)
     exact (Rate.add (show Rate G L ξ (fun x=> ((p+1:ℕ):ℝ)*v x*(f x^(p+1))) from by simpa only [zero_mul,add_zero,mul_assoc] using! ((hv.mul_left (↑(p+1:ℕ))).mul (hf.pow (p+1)))) (hZ'.mul_left _))
   have he : Rate G L ξ PP:= by
     have h:Rate G L 0 (fun x=> (((k:ℝ)^n)^(p+1)*hCost (|Y x|) p k n')):= by
       simpa only [hCost,zero_mul] using! ((((hY.compare (v:=fun x=> |Y x|) (Eventually.of_forall fun x=>(abs_abs _).le)).pow (p+1)).mul_right _).mul_left _)
     apply (((Rate.power (G:=G) (a:=castRank n' m)).mul h).mul (h₀.pow n')).weaken
     unfold castRank ξ; linarith only [hV] -- n'
   filter_upwards [HA,(hq.add he) _ (show ξ<chip (m+1)-9*slack by unfold ξ slack; linarith), Fan.dimes Q L W o hR,Fan.dozing Q L W o hM ξ,(YM.Work.E09.betaF_growth G L).eventually_ge_atTop 1
     ] with t ht hv hg hh hc
   intro β w c f S T hS hT R μ σ H U A he χ C d' v₀ V A' a Y' B' q₁ j k' K r φ V₀ hΦ hΞ u x hF heq
   have hP:1≤ β:=hc; have hx:0<β:=zero_lt_one.trans_le hP; have hw : 0<w:= Real.rpow_pos_of_pos hx _
   have hh' j i (hi:i∈ A j):= hΞ j i hi
   have hx' (F: Tree.Forest S.ratio)(X : Coat T F)(he:X.x=t): (timeΛ X x).manifest:=by
     change ∅=RG.flags (Pressure.temp X.x) _; rw [he]; exact hF.symm
   let P:ℝ:= castRank n' m; let Z':=Field.stock A V₀
   have hL i:= (he i).2.2.2.1
   have hr (k:ℕ)(i:Slots p) (h:Sum.inl k∈ A i): r k≤ m:= (hΞ i (.inl k) h).1.1 -- edit
   have hΨ y (h:y∈Metric.ball 0 w): Brush n' ((Z'*β^P)* (((k:ℝ)^n)^(p+1)* hCost (|Y t|) p k n')) 1 (fun y=> rune H A y k r χ m) y := strength H A β r V₀ y m hk hL (fun i k h=> hΞ i k h|>.2.1) hP (fun i k=>hr k i) hΦ (fun i f' F z=> ht c f S T hS R μ σ H _ ((Greenbelt.prism T t χ o.K 1 (Greenbelt.allot F)).taggedL z) rfl rfl (Field.pin (A i) H) r φ (he i|>.2.2.2.2) (A i) f' (fun j hi=> hh' _ _ hi|>.1) (hL i) (fun x hi=> hΞ _ _ hi |>.2) y (mem_ball_zero_iff.mp h)) (abs_nonneg _)
   have h:= hΨ x (mem_ball_zero_iff.mpr heq)
   have hr:= LocalLTE.pays (j:=n') hw (show w≤1 from ?_) h.nonneg (n:=n') le_rfl (fun y hy=> (hΨ y hy).smooth) (by
        intro y hy j hJ hj;  have h:=(hΨ y hy).order j hj; simpa only [one_pow,mul_one] using h) x (mem_ball_zero_iff.mpr heq)
   rotate_left
   · exact Real.rpow_le_one_of_one_le_of_nonpos hP (le_of_lt ‹v<0›) -- edit
   have hC := foreword H K A U x u rfl β hP r V₀ hk hF hT (by
     intro F X hx hK i j hi; obtain ⟨h,h₁,h₂⟩:= hΞ i j hi; exact ⟨h₁,h₂,fun b=>hg c f S T R μ σ H F X hx hK x r φ b j _ _ _ _ h (hx' F X hx)⟩) (fun i=> ⟨hL i, fun F X hx hK=> hh c f S T F X x (Field.pin (A i) H) μ σ R H hx hK (hx' F X hx) (he i|>.2.2.2.2)⟩) (fun i=> ⟨he i|>.1,he i|>.2.1,he i|>.2.2.1⟩) m (show 0 ≤ Z t from Real.rpow_nonneg hx.le _)
   have hF:= norm_sub_le_norm_sub_add_norm_sub (∏ i,leaflet H χ (increment 1 u) (U i)) (rune H A x k r χ m) (Field.forecast H A m k r χ x)
   have hZ:0≤Z':= prod_nonneg fun i _=> oil_nonneg A (fun k _ h=> hΞ k _ h|>.2.1) _
   apply hF.trans ((add_le_add hC hr.bound).trans (le_trans ?_ (mul_le_mul_of_nonneg_left ((le_abs_self _).trans hv) hZ)))
   apply le_of_eq; ring -- edit
end YM.LocalLTE.Fan.Field
