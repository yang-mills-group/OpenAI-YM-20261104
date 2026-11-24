import YM.Gaps1020.Local.MarkedEconomy
import YM.MergeProof.Revenue
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Blush.Little
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Thermal1020.Shared
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open March Next.Foundations YM.GapsLocal.ExpShares
open PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {j n k M : ℕ} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {R : Rep G f}
variable {X : Coat T F} {I : Finset (Bond f)} {η r q Y W A B A' a β b p v d t γ C s C' μ g ρ ℓ : ℝ} {l:ℕ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi} {Ñ : ChartRatio G}
variable {E:Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable {z : Air f G} {V:E→ Config G c}{x:E}

variable {H : Cash W s μ L Q o C T R}

open PhysicalNext.Repeat.Lotus

open YM.RG01.Survive
variable {ι:Type}[Fintype ι]
open Merge Palette PhysicalNext.Repeat.Daisy
open Push.AbsoluteSums.Mixed Push.AbsoluteSums.Reserves
variable (N:Captain H j C' d v Y A b r B q k χ)(U:ι→Team R)(M':ι→Leaf R)
    (rA:ι→ℝ)(X:Utopia H j v d r C' χ)
local notation "I'" => Tickets (Palette.sign M' S)
open Trees Daisy.Charity.RG12
-- selected budget, keep a δ exponent for all positional purchases. Lifts ∑
-- choices simultaneously in BOTH moment×marker products.
def value (Q:ConnectedActivityE6.Target G P)(L:Side)(μ s B ρ:ℝ)(k j M:ℕ):= Q.goal L s + (2^j*(M+2:ℝ))*entrances Q L μ s B ρ k j M

def combined (M:ℕ)(ρ Z:ℝ) (p:H.ThinP):= (M+2:ℝ) * sumWeight N M' rA M ρ Z p
lemma readyLog (ρ:ℝ)(M:ℕ)(h:WarnBudget (ρ^(M+1)) N.conduit)(hρ:1 ≤ ρ) (Γ:Target.Expense Q)(hB:Bikes Q L μ s Γ.earn (Height.asset Γ) B j k)(hd:degreePrice (radiusB s) (ρ*(swing Q L μ 1 s 0).rootHit) Q.δ≤1/2)(hx: degreePrice (radiusB s) (value Q L μ s B ρ k j M) (Height.asset Γ)≤1/2)(ha : Thermal.BuysMix M' H rA):
    Ready H.smallAt (radiusB s) (fun p=>2^j * combined N M' rA M ρ (ρ^(M+1)) p) (Γ.earn+Height.asset Γ) (value Q L μ s B ρ k j M) (Height.asset Γ) (1/2):=by
  let θ := 2^j*(M+2:ℝ); let A' := entrances Q L μ s B ρ k j M; have hr:0 ≤ θ:=by unfold θ; positivity
  have hw := H.laws.data.funds.length_eq
  have hp:=(Shared.income N M' rA ha ((show (swing Q L μ R.beta s C').Buy S.patch.L Q.halo (radiusB s) from hw.symm ▸ hB.rev _ _ (hw ▸ N.conduit.lives))) (zero_lt_one.trans_le hρ) hd h (one_le_pow₀ hρ) M)
  let a i:=sumWeight N M' rA M ρ (ρ^(M+1)) i; have hv(i):0≤a i:= sumWeight0 N M' rA M _ _ (by linarith) (by positivity) ha.nonnegative i
  have hf:0≤ A':= budget_nonneg (hp 0)
  refine ⟨add_pos_of_pos_of_nonneg (show 0<Q.goal L s from arable H) (mul_nonneg hr hf),hB.allow,hx,by norm_num, fun i=>?_,fun i=>?_⟩
  · unfold combined; exact mul_nonneg (by positivity) (mul_nonneg (by positivity) (hv i))
  refine budget_loosen (budget_mono (budget_scale hr (hp i)) (fun p=> ?_) (fun p=> ?_)) (le_add_of_nonneg_left (arable H).le)
  · split
    next=> unfold combined; exact mul_nonneg (mul_nonneg (by positivity) (mul_nonneg (by positivity) (hv _))) (Real.exp_pos _).le
    next=> exact le_rfl
  dsimp only; split
  next h=> unfold θ combined; simp_rw [← mul_assoc]; refine mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right hB.win (Nat.cast_nonneg _))) (mul_nonneg hr (hv _))
  next h=> rw [mul_zero]
section rate
open Mallow
local notation "b0" => ray+Q.rate
local notation "R0" => horizonRadius G L
variable (L)(μ:ℝ)(Q:ConnectedActivityE6.Target G P)(hm:0<μ) (B r : ℝ→ℝ)(hr : Rate G L 0 B)(hz:Rate G L 0 r)(hh:ray+Q.rate<0)
omit [Fintype ι]
include hm hr
lemma valueRate (M k j:ℕ): Rate G L (ray+Q.rate) (fun x=>value Q L μ x (B x) (R0 x) k j M) := by
  let u:=R0
  let f q (y:ℝ→ℝ) x:=swingTab Q L μ x (u x) q (y x) k
  let y x := Reserves.treeYield (u x*(swing Q L μ 1 x 0).rootHit) (1/2) 0
  have h: Rate G L (ray+Q.rate) y:= by unfold y Reserves.treeYield; rw [pow_zero]; simp only [mul_one]; exact (root10 Q L μ hm u (b:=ray) Rate.power|>.2).mul_right _
  have hu: Rate G L ray u:=Rate.power; let a:=-ray*↑(M+1); have hh:-(ray*((M:ℝ)+1))=a:=by unfold a; push_cast; ring
  have h0: Rate G L (ray+Q.rate) (f 0 (fun _=>0)) := by unfold f swingTab; simp only [Nat.cast_zero,mul_zero]; exact h.mul_left _
  have h1: Rate G L a (fun x=> Real.exp (-Q.mark L μ x)):=by simpa only [syrup,one_mul] using (Mallow.infuso (G:=G) L 1 (μ/4) 1 (by linarith) zero_lt_one a)
  have he {y:ℝ→ℝ}(hp: Rate G L (a+(ray+Q.rate)) y): Rate G L (ray+Q.rate) (fun x=> (u x)^(M+1)*y x):=by convert! (hu.pow (M+1)).mul hp using 1; unfold a; ring
  have hp: Rate G L (a+(ray+Q.rate)) (f 1 (fun _=>0)):= by
     unfold f swingTab extract; simp only [Nat.cast_one,mul_one,mul_zero,zero_sub]; exact (h1.mul_left _).mul h
  have h2: Rate G L (a+(ray+Q.rate)) (f 0 (fun x=> (till x:ℝ))):=by
     unfold f swingTab extract; simp only [Nat.cast_zero, mul_zero,sub_zero]; exact ((Rate.cutoff Q.usable).mul_left _).mul h
  let b x:=entrances Q L μ x (B x) (R0 x) k j M
  have hy: Rate G L (ray+Q.rate) b:=by simpa only [zero_add] using! (hr.mul_left (packets j M M)).mul ((h0.add (he hp)).add (he h2))
  exact ((Rate.power (G:=G) (L:=L) (a:=Q.rate)).weaken (le_add_of_nonneg_left (by norm_num [ray]))).add (hy.mul_left _)
omit hm hr
include hh hz
lemma chargePaid (j:ℕ): ∀ᶠ x in atTop, Thermal1020.charge Q L x (r x) j (till x) ≤ (R0 x)⁻¹:=by
  have he': Rate G L 0 (fun x=> (till x:ℝ)):=by
    apply Rate.radius_price.compare; filter_upwards with x; rw [abs_of_nonneg (Nat.cast_nonneg _),abs_of_nonneg (Nat.cast_nonneg _)]; gcongr; exact Nat.div_le_self _ _
  let f:=fun s=> Thermal1020.charge Q L s (r s) j (till s)
  have h: Rate G L Q.rate f:= by unfold f Thermal1020.charge; have h:= hz.mul (he'.mul_left 2); rw [zero_add] at h; simpa only [zero_mul,add_zero] using! (Rate.power.mul (((Rate.const 1).add h).pow j))
  filter_upwards [((Rate.power (a:=ray)).mul h).below hh 1 zero_lt_one,Delay.shift_pos G L] with s hs ht; have hv:0<R0 s:=Real.rpow_pos_of_pos ht _; change f s ≤ _; rw [← one_div,le_div_iff₀ hv,mul_comm]; exact (le_abs_self _).trans hs
end rate
local notation "R₀" => horizonRadius G L
open Mallow
local notation "μs" => (Thermal1020.charge Q L s)
structure MixReceipt {s:ℝ} (Γ:Target.Expense Q) (D : RG.Stage) (M : ℕ) {B v Y d q C' A a r : ℝ}
    {X' : Cash W s μ L Q o C T R}(N:Captain X' D.order C' d v Y A a r B q k χ) : Prop where
  large : 2≤ horizonRadius G L s
  turns : HasClutch N.conduit A
  chargeFits : Thermal1020.charge Q L s r D.order (till s) ≤ (horizonRadius G L s)⁻¹
  Warn : WarnBudget ((horizonRadius G L s)^(M+1)) N.conduit
  shared : Flock X' N.conduit A B k
  book : Bikes Q L μ s Γ.earn (Height.asset Γ) B D.order k
  meet : degreePrice (radiusB s) ((horizonRadius G L s)*(swing Q L μ 1 s 0).rootHit) Q.δ≤1/2
  funds : degreePrice (radiusB s) (value Q L μ s B (horizonRadius G L s) k D.order M) (Height.asset Γ)≤1/2
  expCredit : collars G (Height.asset Γ) s D.order D.power*(value Q L μ s B (horizonRadius G L s) k D.order M*(1-1/2:ℝ)⁻¹) ≤ 1
  forceCredit : Mallow.straw μ L G s ≤ ((horizonRadius G L s)^(M+1))⁻¹ * Blush.glyph s

omit [Fintype ι]
structure JointMarket (Q:ConnectedActivityE6.Target G P)(Γ:Target.Expense Q)(L:Side) (W μ:ℝ) (ξ:Target.Order G W) (D:RG.Stage) (J:ℕ) (s:ℝ): Prop where
  flock : foam Q L
  enough : Tariff Q L J μ s
  cost m (_:m≤J) (c f:Side)(S:StepData c f)(T:Tube G S) (hT:Stamp T)(R:Rep G f)(C:ℝ)(U:Cash W s μ L Q ξ C T R):
    ∃ (A a v t d w B q C' :ℝ)(k:ℕ) (N:Captain U D.order C' d v t A a w B q k Chi.canonical), MixReceipt Γ D m N
lemma access (Q:ConnectedActivityE6.Target G P)(Γ:Target.Expense Q):∃ n:ℕ,∀ (L:Side), n≤L.val→ ∀ W μ o D i, Γ.wanting≤-(7/16:ℝ)→0<W→0<μ→∀ᶠ s in atTop, JointMarket Q Γ L W μ o D i s:=by
  obtain ⟨n,H⟩:= Shared.teamIssued P Q; obtain ⟨n',hn⟩:= Daisy.early Q
  refine ⟨max n n',fun L hL W μ o D i he hW hμ=>?_⟩
  have hh:ray+Q.rate<0:= by unfold ray; linarith [Γ.reach];
  let y₀:=Height.asset Γ; have ha:0<y₀:= Height.asset_pos _
  let Ph (m:ℕ) (s:ℝ):Prop:=∀ (c f : Side)(S:StepData c f)(T:Tube G S), Stamp T → ∀ (R:Rep G f)(C:ℝ)(U:Cash W s μ L Q o C T R), ∃ (A a v t d w B q C' :ℝ)(k:ℕ) (N:Captain U (D:RG.Stage).order C' d v t A a w B q k Chi.canonical), MixReceipt Γ D m N
  have ht (m:Fin (i+1)): ∀ᶠ s in atTop, Ph m s:= by
    by_cases hp:∃ D:Patch,D.Branches P.bind G ∧ D.L=L ∧ D.J=P.j
    swap; · exact Eventually.of_forall fun x c f S T _ R C H=>let h:=H.laws.data.funds; False.elim (hp ⟨S.patch,h.funds.kernel,h.length_eq,h.funds.atStep⟩)
    obtain ⟨R,hR,hL',hr⟩:=hp; let k₀:=m.val; let y:= ray*↑(k₀+1)
    obtain ⟨A,a,C,d,v,t,r,B,q,k,hB,hJ,hO,hP⟩:= H L ((le_max_left ..).trans hL) R hR y (by unfold y ray; positivity) D.order Chi.canonical W hW μ hμ o
    let ρ:= horizonRadius G L; have hx:= valueRate L μ Q hμ B hB k₀ k D.order
    have hZ:= (degree10 L _ hx y₀).below hh (1/2) (by norm_num)
    have hy : Rate G L 0 shiftG := (((Rate.radius_price).mul_left 2).add (Rate.const 1)).mul_left 4
    let c:=fun s=> collars G y₀ s D.order D.power
    have hc: Rate G L 0 c := by simpa only [zero_mul] using! ((hy.pow (D.power*D.order)).mul_right (Reserves.polyPrice y₀ (D.power*D.order)))
    have hp:= hc.mul (hx.mul_right ((1-1/2:ℝ)⁻¹)); rw [zero_add] at hp
    have hb := stables L Q hμ B ha (v:=Γ.earn) (by unfold y₀ Height.asset; linarith) Γ.price hB D.order k D.power
    have hP₀ : Rate G L (-1) (fun x=> (ρ x)^(k₀+1) * ((Blush.glyph x)⁻¹ * Mallow.straw μ L G x)):= by
       convert! ((Rate.power (a:=ray)).pow (k₀+1)).mul (Blush.efferv (L:=L) (G:=G) hμ (-1-y)) using 1; unfold y; ring
    filter_upwards [hP,radiusLarge L,ready10' Q L μ hμ ρ (b:=ray) Rate.power hh,hZ,hp.below hh 1 zero_lt_one, chargePaid L Q r hJ hh D.order, hb, hP₀.below (by norm_num) 1 zero_lt_one] with s hP hh hk hΓ hp hS hG hΓ' c f S T hT U C' Y
    obtain ⟨N,h0,h₁,h₂⟩:= hP _ _ S T ((Y.laws.data.funds).patch hL' hr) hT U _ Y
    have hD : 1≤ρ s:= by change 2 ≤ ρ s at hh; linarith
    have h : WarnBudget ((ρ s)^(k₀+1)) N.conduit:= by rw [show (ρ s)^(k₀+1)=betaF G s L ^ y from (Real.rpow_mul_natCast hG.1.paid.le _ _).symm]; exact h₂
    refine ⟨A,a,v s,t s,d s,r s,B s,q s,C,k,N,⟨hh,h₁,hS,h,h0,hG.1,hk.2,(le_abs_self _).trans hΓ,(le_abs_self _).trans hp,?_⟩⟩; have hb₁:0 < Blush.glyph s := by exact Blush.glyphpos s
    have hp₁:0<ρ s^(k₀+1):=by positivity
    have hw:= (le_abs_self _).trans hΓ'; change ρ s^(k₀+1)*((Blush.glyph s)⁻¹*Mallow.straw μ L G s)≤1 at hw
    rw [mul_comm (_⁻¹), ← div_eq_mul_inv,le_div_iff₀ hp₁]
    field_simp at hw; linarith
  filter_upwards [eventually_all.mpr ht,thaws Q L i μ hμ] with s hs h'; exact ⟨hn L ((le_max_right ..).trans hL),h',fun m h=> hs ⟨m,Nat.lt_succ_of_le h⟩⟩
def markerBudget (G:Gauge): Decal G := ⟨fun _ Q Γ L W μ o D i s=> JointMarket Q Γ L W μ o D i s,fun _ Q Γ=> access Q Γ⟩
end YM.ConnectedActivityE6.Blaze.Thermal1020.Shared
