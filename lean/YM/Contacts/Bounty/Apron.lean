import YM.Contacts.Bounty.Primes
import YM.Contacts.Bounty.Escrow
/-! # Loom geometry and post-L jobs before inputs over ALL tori. D generalized stencils & park costs. -/
noncomputable section
set_option autoImplicit false
namespace YM.PhysicalNext.Repeat.Meadow
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
-- adjusted from Equip/Storeys for power arbitrary.
lemma phenom (G : Gauge) (L : Side) (B:Stage) (k : ℝ) (_he: 0 < k) : ∃ q: ℝ→ℝ, Rate G L (-(1/2)) q ∧ ∀ᶠ t in atTop,
    ∀ P : BudgetPoint,P.power=B.power→P.order=B.order→ P.supportExponent=B.supportExponent→ P.threshold ≤ 2*Pressure.fiery G t L→∀ β b Λ, |β|≤4*Pressure.betaF G t L→|b|≤ k→0 ≤ Λ→ Λ≤ ConnectedActivityE6.loopBill G L t→
      Song.octaveNeed G P B.clip B.width B.paths Λ β b ≤ q t := by
  by_cases hs: ∃ p:BudgetPoint,p.power=B.power ∧ p.order=B.order∧p.supportExponent=B.supportExponent
  swap
  · exact ⟨_,Rate.power (G:=G) (L:=L),Eventually.of_forall fun t P hp hq hE => (hs ⟨P,hp,hq,hE⟩).elim⟩
  obtain ⟨p,hp,hq,hE⟩:=hs
  let c:=B.paths; have hc:0≤c:=B.paths_pos.le -- inspect
  let T t:=2*Pressure.fiery G t L
  let K t:=4*Pressure.betaF G t L
  let s i:= anchoredFee (headline p) i -- edit
  let f i t a b:= s (octave i)*(|VerifiedReset.factor| *a*(turnFee p*(highFee G i p B.width*T t^i*b)))
  let q t:= s Geo.lowCount*(|VerifiedReset.factor| *k*(turnFee p*T t^2*(lowFee G p B.width * lowerSize B.clip c)))+(f 3 t (K t) c+(f 4 t (K t) c+ f 2 t 1 (ConnectedActivityE6.loopBill G L t)))
  have ht:Rate G L (-(1/2)) T:=Rate.flame.mul_left _
  have hv:Rate G L 1 K:= Rate.hat.mul_left _
  have hK : ∀ (b:ℕ) (A : ℝ→ℝ) (B:ℝ) (U : ℝ→ℝ) (a:ℝ), Rate G L B A→Rate G L a U→ B+(-(1/2:ℝ)*b+a) ≤ -(1/2:ℝ)→ Rate G L (-(1/2)) (fun t=>f b t (A t) (U t)):= by
    intro i A B X a he hK hs; exact (Rate.mul (he.mul_left |VerifiedReset.factor|) (((((ht.pow i).mul_left _).mul hK)).mul_left _)|>.mul_left _).weaken hs
  refine ⟨q,Rate.add ?_ ((hK _ _ _ (fun _=>c) _ hv (Rate.const c) (by norm_num)).add ((hK _ _ _ _ _ hv (Rate.const c) (by norm_num)).add (hK 2 _ _ _ _ (Rate.const 1) (ConnectedActivityE6.loopBill_rate G L) (by norm_num)))),?_⟩
  · exact ((((((ht.pow 2).mul_left _).mul_right _).mul_left _).mul_left _)).weaken (by push_cast; norm_num)
  exact Eventually.of_forall fun t P h H hv ht b B' Λ hx hβ hΛ hK=> Meadow.rain G _ B.width_pos hc p P ⟨h.trans hp.symm,H.trans hq.symm,hv.trans hE.symm⟩ hx hβ ht hΛ hK
lemma steppes (G:Gauge) (L:Side) (X : Stage) (W ω₁ : ℝ) (hw : 0 < W): ∀ᶠ t in atTop,∀ p:BudgetPoint,p.threshold ≤ 2*Pressure.fiery G t L→p.power=X.power→p.order=X.order→p.supportExponent=X.supportExponent→p.B= radiusB t→∀ β b Λ,|β| ≤ 4*betaF G t L→|b| ≤ W→ 0≤ Λ→ Λ ≤ ConnectedActivityE6.loopBill G L t →
    let u:=Song.octaveNeed G p X.clip X.width X.paths Λ β b
    u ≤ betaF G t L ^ (-(7/16):ℝ) ∧ Real.exp (-(X.width/4)*p.B)*u ≤ betaF G t L ^ (ω₁:ℝ) ∧ preExponent p/p.B≤ X.width/4:= by
  obtain ⟨q,hq,h⟩:= phenom G L X W hw
  have he : Rate G L ω₁ (fun x=> Real.exp (-(X.width/4)*radiusB x)) := by
    refine (Rate.cutoff (G:=G) (L:=L) (a:=ω₁) (show 0<X.width/4 from div_pos X.width_pos (by norm_num))).compare (Eventually.of_forall fun x=>?_)
    rw [abs_of_nonneg (Real.exp_nonneg _),abs_of_nonneg (Real.exp_nonneg _)]; apply Real.exp_le_exp.mpr; exact mul_le_mul_of_nonpos_left (show (Pressure.Stores.till x:ℝ)≤radiusB x by exact_mod_cast Nat.div_le_self ..) (by have he:=X.width_pos; linarith)
  filter_upwards [h,(he.mul hq) ω₁ (by linarith), hq (-(7/16)) (by norm_num), (((tendsto_const_nhds (x:=X.supportExponent+3)).div_atTop (tendsto_natCast_atTop_atTop.comp YM.Work.E01.radiusB_tendsto)).eventually (gt_mem_nhds (show 0<X.width/4 from by have he:=X.width_pos; linarith)))] with x h ht hz hy p hV hp hx hX hB β b Λ ha hw hS hh u
  have hf : u≤ q x:= h p hp hx hX hV β b Λ ha hw hS hh -- implicit
  refine ⟨hf.trans ((le_abs_self _).trans hz),?_,?_⟩
  · rw [hB]; exact (mul_le_mul_of_nonneg_left hf (Real.exp_nonneg _)).trans ((le_abs_self _).trans ht)
  unfold preExponent; rw [hX,hB]; exact le_of_lt hy
end YM.PhysicalNext.Repeat.Meadow
namespace YM.Contacts.Bounty
open AnalyticBridge VerifiedReset Collection Quotes Revest
open PhysicalNext.Repeat PhysicalNext.Repeat.Roost Terrain
open Function Filter Lattice Wilson RG Pressure Ovens Ovens.Pipes Residual WilsonStartup UVNext.PricedKernels Averaging Geo Progress.DirectedRecipe Extra.Iteration Org
open UVNext.CouplingReset Push Push.AbsoluteSums Animals Precision RG.Supply Input RG.Shoot PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open Next.Scheduling PhysicalNext.ThroughLaunch Time Model Arbor Province.Costing Tucks Milling.Steam
open Pulse ConnectedActivityE6 Testing SectorMeasure Presented Coat Blaze Blaze.March
open Pane Boulevard Poetry Song Deck Further.PhysicalPeriodLimitF933 Macrame Trio
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{l q r v t b α β:ℝ}
namespace Trophy.Lore
variable {M: Metals G}{D:Rolls M.p}(A:Alloy M D)(B:Factor A) {c f c' f':Side}{i j l k N n m o:ℕ}
section loom
def dot (l o z u:ℕ):= 8*(Poetry.studio l z u o) +200*(1+z+u+z)
def dim (l o:ℕ) := dot l o 1 2
lemma heritage {z b:ℕ} (h:z>0) (hb:b≤2*z):
    dot l o z b ≤ dim l o * z:= by
   let K:= Poetry.generous l z b; let F:= Poetry.generous l 1 2; let U:= Poetry.roomP l 1 2 o; let T:=o*(o+1); have he:K ≤ F*z:= by unfold K F Poetry.generous Mint.width; nlinarith only [h,hb]
   have hh: Poetry.roomP l z b o ≤ U*z:= by change T*(4*K+2)+2*K ≤ (T*(4*F+2)+2*F)*z; nlinarith only [Nat.mul_le_mul_left T he, Nat.mul_le_mul_left T h,he]
   unfold dot dim Poetry.studio; unfold dot Poetry.studio; dsimp [U] at hh; nlinarith only [hh,hb,h]
lemma gym (a b:ℕ): a*b ≤ Trio.tent a b:= by unfold Trio.tent Meadow.studio Meadow.roomSize Mint.width; omega
variable (m o)
local notation "u₀" => A.B.a.clock.J (m+1)
local notation "l₀" => A.B.a.clock.J m
set_option quotPrecheck false
local notation "a" => dim (B.target u₀ l₀|>.halo) o
local notation "z" => radiusB (A.B.a.clock.hatBeta m)
-- naming.
abbrev cape := dim (B.target (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)|>.halo) o
-- define later use?
variable {A B o m}
lemma ceiling (hp:(A.B.a.budget (m+1)).B ≤ 2*(A.B.a.budget m).B) : certificate A B m o ≤ Trio.tent (a) z:= le_trans (heritage (l:=(B.target u₀ l₀|>.halo)) (o:=o) (A.B.a.budget m).B_pos hp) (gym ..)
-- from optional after.L shells. 
lemma wholeV (hb:Trio.maxFixed (cape A B m o) ≤ A.delay.shells (A.B.a.clock.J (m+1))) : 2*Trio.base (a) z < (A.B.a.S.side m n).val:= by
   let b:=dim (B.target u₀ l₀|>.halo) o; let J:=A.B.a.clock; let V:=z; let K:= A.delay.growth (u₀); have hv : 1≤ z:= (A.B.a.budget m).B_pos; have hk:0< Trio.maxFixed b:= by unfold Trio.maxFixed Trio.base; omega
   obtain ⟨_,hh⟩:=B.inn.terms.sizes _ _ (PriceCompiler.step_paid A.B.a m); have hx:= A.B.valid.volume m n;
   apply lt_of_le_of_lt (Trio.roof b z hv); apply lt_of_lt_of_le _ hx; change _< A.delay.shells u₀ * (1+V+J.coverSize (m+1))^K; apply lt_of_lt_of_le _ (Nat.mul_le_mul_right _ hb); apply Nat.mul_lt_mul_of_pos_left _ hk; exact lt_of_lt_of_le (b:=1+V+J.coverSize (m+1)) (by omega) (le_self_pow₀ (by omega) (by change 1≤K at hh; omega))
end loom
end Trophy.Lore
end YM.Contacts.Bounty
