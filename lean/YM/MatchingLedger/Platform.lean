import YM.MatchingLedger.Needle
import YM.MatchingLedger.Top
/-!
# All-period post-L implementation

Before identifying coefficients, price rare events under the *actual* law of the first step.
No coherence assertions between witnesses from different purchases.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MatchingLedger.Home
open Function Filter Set MeasureTheory Lattice RG Wilson Tree Pressure
open PatchArea Action Cooling Pins Top
open scoped Topology Classical BigOperators Matrix.Norms.Frobenius

variable {G:Gauge}

def coeff (P : Patch)(K : KernelChoices) (G : Gauge) := fee 4 (lowerCost G P K)⁻¹ (upperCost G P K)
lemma coeff_nn (P : Patch)(K : KernelChoices) (G : Gauge) : 0≤coeff P K G := fee_nonneg _ (inv_pos.mpr (zero_lt_one.trans_le (lower_pos G P K))).le (zero_le_one.trans (upper_pos G P K))

def clock (b : ℝ):=1+Real.log (8*b)
lemma clock_one {b:ℝ}(h:2≤b) : 1≤ clock b := le_add_of_nonneg_right (Real.log_nonneg (by linarith only [h]))

def earned (P : Patch)(K : KernelChoices)(G : Gauge) (b:ℝ) : Prop :=
  2≤b ∧ macroR P ≤ radiusB b ∧ lowerCost G P K≤clock b ∧
  ∀ t:ℝ, 1 ≤ t→ t^2≤ 2*b → ∀ u:ℝ, 0≤u → coeff P K G * Cooling.spread G P K t u ≤ (clock b)^2 * (u+1)

lemma wired (P : Patch)(K : KernelChoices) (G : Gauge): ∀ᶠ b:ℝ in atTop, earned P K G b := by
  have ht:Tendsto clock atTop atTop:= tendsto_atTop_add_const_left atTop 1 (Real.tendsto_log_atTop.comp (tendsto_id.const_mul_atTop (by norm_num : (0:ℝ)<8)))
  let u:=upperCost G P K; let W:= (linkRent P : ℝ);
  let a:ℝ:= park (depth P)*(1+u*park (belt P)); let d:=park (depth P)*(u*W+W*Module.finrank ℝ G.Mat)
  filter_upwards [eventually_ge_atTop (2:ℝ), Work.E01.radiusB_tendsto.eventually_ge_atTop (macroR P),
    ht.eventually_ge_atTop (lowerCost G P K), ht.eventually_ge_atTop (coeff P K G * d), ht.eventually_ge_atTop (coeff P K G*a)] with b hb he hl hZ hz
  refine ⟨hb,he,hl,fun t ht h L hp=>?_⟩
  have hv : tax G P t ≤ W*Module.finrank ℝ G.Mat*clock b:= by
    refine mul_le_mul_of_nonneg_left ((Real.log_le_log (by linarith only [ht]: 0<(4:ℝ)*t) ?_).trans (le_add_of_nonneg_left zero_le_one)) ?_
    · nlinarith only [ht,h]
    positivity
  let Y:=clock b; have hy:1≤Y:=clock_one hb
  have hh : Cooling.spread G P K t L ≤ a*L + d*Y:=by
    unfold Cooling.spread a d; have hx : u*W≤ u*W*Y:=le_mul_of_one_le_right (by unfold u W; positivity [zero_lt_one.trans_le (upper_pos G P K)]) hy
    have hx':=park_nn (depth P)
    unfold u W Y at *; linarith only [mul_le_mul_of_nonneg_left hv hx',mul_le_mul_of_nonneg_left hx hx']
  apply le_trans (mul_le_mul_of_nonneg_left hh (coeff_nn P K G))
  rw [mul_add]; change coeff P K G*(a*L)+coeff P K G*(d*Y) ≤ Y^2*(L+1)
  have hh' := mul_le_mul_of_nonneg_right (le_trans (show _≤ Y from hz) (le_mul_of_one_le_right (zero_le_one.trans hy) hy)) hp
  nlinarith only [hh',mul_le_mul_of_nonneg_right hZ (zero_le_one.trans hy)]

def invite (G : Gauge) : After G where
  wants P K _ x:= earned P K G x
  sustained _ P K _:=wired P K G

def ruler (C:Family G)(i:ℕ) := clock (C.path.levels.clock.hatBeta (i+1))

variable (C:Family G) (m p:ℕ)
local notation "S" => stepTor C m p
local notation "H" => C.path.rep (m+1) p m
local notation "D" => C.path.rep (m+1) p (m+1)
local notation "K" => C.path.levels
local notation "Y" => ruler C m
local notation "β" => C.beta (m+1) p
local notation "t" => frost C m p
variable (hp : Prepared (invite G) C.path.levels)(hC:C.Makes)
include hp hC
lemma wake : 1≤ t ∧ 1≤Y ∧ InRange S ∧ ∀ L:ℝ,0 ≤ L →
      (coeff (S).patch (S).kernel G) * Cooling.spread G (S).patch (S).kernel t L ≤ Y^2 * (L+1) := by
  obtain ⟨h,h₁,_,h₂⟩ := (show earned (S).patch (S).kernel G ((K).clock.hatBeta (m+1)) from hp m p 0 (Nat.zero_le _))
  have hv := (hC.wilson.represents (m+1) p (m+1) le_rfl).band
  have ht : 1 ≤ t := Real.one_le_sqrt.mpr <| (show (1:ℝ) ≤ _/2 by linarith only [h]).trans hv.1
  refine ⟨ht, clock_one h,⟨?_,?_⟩,h₂ _ ht (by rw [frost_beta C m p hC]; exact hv.2)⟩
  · have hm : macroR (S).patch ≤ (K).clock.coverSize (m+1) := h₁
    apply le_trans _ ((K).fits.sizeT (m+1) p); gcongr; omega
  have hh := (K).fits.sizeT m p; omega

lemma certified (F : Forest (stepTor C m p).ratio) (V : Config G (C.side m p)) (R : Support (C.side m p))(L : ℝ) (hl : 0 ≤ L) (hV : ∀ i, t^2*outside V i ≤ L) :
    pressureBill (F.order G) (Cooling.weight F V t) (fun x=> (Y)⁻¹*shock F R t x) ≤
      R.card * ((Y)^2 * (L+1)):= by
  obtain ⟨ht,hY,hI,hU⟩:=wake C m p hp hC; let Q':= coeff (S).patch (S).kernel G
  have hx:= (show earned (S).patch (S).kernel G ((K).clock.hatBeta (m+1)) from hp m p 0 (Nat.zero_le _)).2.2.1
  refine (pressure_mono (weight_pass F V t ((K).blocks m p).branches) ((Envelope.const _).mul (bounded F R t)) ((Envelope.const _).mul (bounded F R t)) (fun v=> mul_le_mul_of_nonneg_right (inv_anti₀ (zero_lt_one.trans_le (lower_pos G (S).patch (S).kernel)) hx) (show 0 ≤ Cooling.shock F R t v from mul_nonneg (sq_nonneg _) (total_nn (links_nn _ _))))).trans ?_
  apply le_trans (Cooling.front F hI R V t ((K).blocks m p).branches ht L hl hV); rw [mul_left_comm (fee ..)]; exact mul_le_mul_of_nonneg_left (hU L hl) (Nat.cast_nonneg _)

-- concise consumer claim keeps density identity visible; re-run same proof after purchasing more.
structure Front (C:Family G) : Prop where
  issued (m p:ℕ) :
    1 ≤ ruler C m ∧ 1 ≤ frost C m p ∧ InRange (stepTor C m p)
  cooled (m p:ℕ)(F : Forest (stepTor C m p).ratio) (V : Config G (C.side m p)) (R: Support (C.side m p))(L:ℝ): 0≤L → (∀ i, frost C m p^2*outside V i ≤ L) →
    pressureBill (F.order G) (Cooling.weight F V (frost C m p)) (fun x=> (ruler C m)⁻¹* shock F R (frost C m p) x)≤
        R.card * (ruler C m^2*(L+1))
  physical (m p:ℕ)(F : Forest (stepTor C m p).ratio)(V:Config G (C.side m p)) (g:Config G (C.side (m+1) p)→ℝ)(h:Envelope g) (hg:GaugeInvariant g):
    let L:= stepTor C m p; let Bb:= C.path.rep (m+1) p m; let w:= Cooling.weight F V (frost C m p)
    Weight (F.order G) w ∧ 0<Bb.eval V ∧ L.push (C.beta (m+1) p) (fun x=> g x*(C.path.rep (m+1) p (m+1)).eval x) V / Bb.eval V = weigh (F.order G) w (g∘ F.drape)

lemma plat : Front C := ⟨fun m p=>⟨(wake C m p hp hC).2.1,(wake C m p hp hC).1,(wake C m p hp hC).2.2.1⟩,
    fun m p=> certified C m p hp hC, fun m p F V _u hu h=> portrait C m p hC F V hu h⟩

omit hp hC
open OPE PhysicalNext.Repeat.Daisy.Charity.RG12
/-- This is a producer, no supplied thermal or matching premise. Use before choosing periods and
perturbative truncation, and with any other (e.g., burst) decals and Needle requests. -/
theorem production (δ : Decal G) (N : After G) (hG:G.Simple) (penalty:ℝ) (hs:0<penalty) (order:Extraction.Order):
  let τ:= δ.paired (Pins.thread ((invite G).coin N));
  ∃ (C:Family G)(f:Extraction.Order)(T:Table C.book)(U:Spec.Final C (order.refine f) T) (L:EveryPhase.Almanac U)
      (Q : Prescription U.sector.derivatives),
      C.Makes ∧ C.path.levels.clock.kernel.penalty=penalty ∧ Spec.Calibrated C ∧
      UVExtension.Oasis.Floral (hG:=hG) C ∧ (Extraction.Order.mk Extraction.Sequence.full (order.refine f).per).Ordered C T ∧
      EveryPhase.Completed U L ∧ Facilities C (order.refine f) T ∧ Nonempty (UVExtension.Mast.Couture C hG τ) ∧ Q.Coherent ∧ AllShapes U Q ∧ Prepared N C.path.levels ∧ Front C := by
  intro τ
  obtain ⟨C,f,T,U,L,hC,hW,hP,hO,hF,hU,hE,hHx,⟨R⟩,Q,hQ,hq,_⟩:= YM.RG12.fashions G τ hG penalty hs order
  have hv:= purchased ((invite G).coin N) R
  exact ⟨C,f,T,U,L,Q,hC,hP,hW,hO,hF,hE,hHx,⟨R⟩,hQ,hq,fun a b p h=>(hv a b p h).2,plat C (fun a b p h=>(hv a b p h).1) hC⟩
end YM.MatchingLedger.Home
