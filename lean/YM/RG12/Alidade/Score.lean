import YM.RG12.Alidade.Teams
import YM.RG12.Frames.Rest
/-!
# Global bound from contiguous lit & single missing-step prices

Not a monotone market price argument dividing by N late (which could miss one arbitrarily large
charge per gap). At `j` lit induct simultaneously from either predecessor `j-1` (sharp-local criterion)
or from the output of the radar insurance card aimed at `j-1` (raw k-cell, insured). Don't
pay for both, don't count gaps over individual i. Doesn't require number of levels through
stage j uniform even vs beta, nor that a single specific lamp is lit on every stage. Reading
consumers still need to tie the `t(i),Y(i)` to same Final and canonical charts.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Alidade
open Function Finset Filter Lattice Wilson RG Real Frames
open scoped Topology BigOperators Classical

variable {d:ℕ}{V:Grade d→ Type}[∀ i,NormedAddCommGroup (V i)][∀ i,NormedSpace ℂ (V i)][FiniteDimensional ℂ (Col V)]
variable {F:Type}[AddCommGroup F][Module ℂ F]
variable {G:Gauge}{Z:Levels G}{t e:ℕ→ℝ}{Y:ℕ → Col V≃ₗ[ℂ] F}{P:Col V≃ₗ[ℂ] F}{g:ℕ→Currency V}{f:ℕ→ℕ}{c:ℕ→Prop}{K:ℝ}{D Q b:ℕ}
local notation "clk"=>epoch Z
-- Notes: assume coin tariffs ANY previously certified steps. Prices only tested on same frames.
-- Can be calibrated independently at nodes without position PT; identification of field charge
-- requires using *same filter* at all points though.
structure Handoff (Z:Levels G) (Y:ℕ → Col V≃ₗ[ℂ] F)(t:ℕ→ℝ)(g:ℕ→Currency V)(e:ℕ→ℝ)(D Q b:ℕ)(i j:ℕ) : Prop where
   pos : 0 < t i/t j
   clock : 1 ≤ t i/t j
   tests (x:Col V): let T:=pot Z D Q e; let A:=pace (Y i) (Y j) (t i/t j) pos
     T i*coins b (g i) (epoch Z i) (A x) ≤ T j*coins b (g j) (epoch Z j) x ∧ T i*coins b (g j) (epoch Z j) (A.symm x) ≤ T j*coins b (g i) (epoch Z i) x

-- two modes of payments
structure Tariff (Z:Levels G)(f:ℕ→ℕ)(c:ℕ→Prop)(Y:ℕ → Col V≃ₗ[ℂ] F)(P:Col V≃ₗ[ℂ] F)(t:ℕ→ℝ)(g:ℕ→Currency V)(e:ℕ→ℝ)(K:ℝ)(D Q b:ℕ) : Prop where
   beacon : Beacon Z f c
   losses : ∀ i,0≤e i
   delays : ∀ i,0 < t i
   spot: ∀ᶠ i in atTop,c i → Fits (g i) K ∧ formative (Y i) P
   relay : ∀ᶠ i in atTop,c (i+1) → (c i → Handoff Z Y t g e D Q b i (i+1)) ∧ (¬ c i → Handoff Z Y t g e D Q b (f i) (i+1))
variable (h:Tariff Z f c Y P t g e K D Q b)(x:F)(L:F→ₗ[ℂ]ℂ)(w:Grade d)
omit [FiniteDimensional ℂ (Col V)] in
lemma at_trim {Y P:Col V ≃ₗ[ℂ] F} (ht:formative Y P)(hl: ∀ x∈prev V w, L (P x)=0)(v:Col V): L (Y v)= L (Y (trimBelow w v)):=by
   rw [← sub_eq_zero,←map_sub,←map_sub]
   let x:=v-trimBelow w v
   have he: x∈prev V w:=by intro i hi; simp [x,trimBelow,hi]
   exact (P.apply_symm_apply (Y x) ▸ hl (P.symm (Y x)) (ht.prev w x he))
local notation "T!"=> pot Z D Q e
local notation "H!" i:max=> Handoff Z Y t g e D Q b i

structure Clearance (Z:Levels G)(Y:ℕ → Col V≃ₗ[ℂ] F)(t:ℕ→ℝ)(g:ℕ→Currency V)(e:ℕ→ℝ)(D Q b:ℕ)(x:F)(L:F→ₗ[ℂ]ℂ)(w u:Grade d) (k:ℕ)(C:ℝ):Prop where
   inward : coins b (g k) (epoch Z k) ((Y k).symm x) ≤ C*(pot Z D Q e k)/(t k)^u.val
   outwards v : ‖L (Y k v)‖ ≤ C*(t k ^w.val)* ((pot Z D Q e k) * coins b (g k) (epoch Z k) (trimBelow w v))

variable {u:Grade d}
-- propagate exact engineering once in each direction
lemma relay {i j:ℕ}(he:Handoff Z Y t g e D Q b i j)(ti : 0<t i)(tj:0<t j) (hp:∀ i,0 ≤ e i)
   (hy : formative (Y i) P)(hy':formative (Y j) P)(hx: P.symm x ∈ flag V u) (hl: ∀ x∈prev V w,L (P x)=0)
   (hi:Fits (g i) K)(hj:Fits (g j) K){C:ℝ}(hz:0 ≤ C)
   (hc:Clearance Z Y t g e D Q b x L w u i C) : Clearance Z Y t g e D Q b x L w u j C:=by
   let r:=t i/t j; let A:= pace (Y i) (Y j) r he.pos; have hR:1 ≤ r:= he.clock
   have ht:=pace_form (Y i) (Y j) hy hy' he.pos
   have hover: A.symm ((Y i).symm x) ∈ flag V u:= by
      apply (triangular_iff_stays V _).mp ht.inv
      rw [← P.apply_symm_apply x]; exact (triangular_iff_stays V _).mp (triangular.inv hy) u _ hx
   let hcoins (i : ℕ):= coins b (g i) (clk i)
   have hI:0 ≤ clk i := zero_le_one.trans (begun Z i)
   have hJ:0 ≤ clk j:= zero_le_one.trans (begun Z j)
   let T:=pot Z D Q e; have hT:0<T i:=zero_lt_one.trans_le (pot_big Z D Q i hp); have hT':0<T j:=zero_lt_one.trans_le (pot_big Z D Q j hp)
   constructor
   · have hb := (he.tests ((Y i).symm x)).2
     let z:= A.symm ((Y i).symm x)
     change T i*hcoins j z ≤ T j*hcoins i _ at hb
     change hcoins j _≤ _
     rw [pace_back (Y i) (Y j) he.pos x]
     have hs:0 ≤ r^u.val:=pow_nonneg (zero_le_one.trans hR) _
     calc
       _ ≤ r^u.val *((T j*hcoins i ((Y i).symm x))/T i) := (grow_price hj hJ hR hover).trans (mul_le_mul_of_nonneg_left ((le_div_iff₀ hT).mpr (by rwa [mul_comm _ (T i)])) hs) -- grows
       _ ≤ r^u.val *((T j*(C*T i/(t i)^u.val))/T i):=by
         apply mul_le_mul_of_nonneg_left _ hs
         exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hc.inward hT'.le) hT.le
       _ = C*T j/(t j)^u.val := by unfold r; rw [div_pow]; field_simp
   intro v
   let y:= dilate r⁻¹ (trimBelow w v)
   rw [at_trim L w hy' hl v, pace_pull (Y i) (Y j) he.pos]
   refine (hc.outwards (A y)).trans ?_
   have hx:T i*hcoins i (trimBelow w (A y))≤ T j*hcoins j y:= ((mul_le_mul_of_nonneg_left (coins_trim hi hI ..) hT.le).trans (he.tests y).1)
   have hr: T i*hcoins i (trimBelow w (A y)) ≤ T j*(r⁻¹ ^w.val*hcoins j (trimBelow w v)):= hx.trans (mul_le_mul_of_nonneg_left (shrink_price hj hJ hR w v) hT'.le)
   have h0:=mul_nonneg hz (pow_nonneg ti.le w.val)
   refine (mul_le_mul_of_nonneg_left hr h0).trans_eq ?_
   change C*_*(_*(_*hcoins _ _))= _ *(T j*hcoins _ _)
   rw [inv_pow]; unfold r; rw [div_pow]; field_simp

include h
set_option linter.unusedSectionVars false in
lemma charted (hL:∀ v ∈prev V w,L (P v)=0)(hX:P.symm x∈flag V u):∃ C:ℝ,0 ≤ C ∧ ∀ᶠ n in atTop,c n → Clearance Z Y t g e D Q b x L w u n C:=by
   -- finitely many origin calibrations suffice, independently bounded in frame units
   obtain ⟨N,hN⟩ := eventually_atTop.mp h.spot
   have he:{j:ℕ| N ≤ f j}∈atTop:= h.beacon.grows.eventually_ge_atTop _
   change ∀ᶠ j in atTop, N ≤ f j at he
   obtain ⟨M,hM⟩:= eventually_atTop.mp (he.and (h.relay.and h.beacon.valid))
   let M':=max M N+2
   have cost(n:ℕ)(hε:N ≤ n)(hn: c n): ∀ᶠ C:ℝ in atTop, Clearance Z Y t g e D Q b x L w u n C:=by
      let T:=pot Z D Q e
      obtain ⟨ho,ht⟩:= hN n hε hn
      let A:= LinearMap.toContinuousLinearMap (E:=Col V) (L.comp (Y n).toLinearMap)
      let c' := coins b (g n) (clk n); have heT:0 ≤ T n:=zero_le_one.trans (pot_big Z D Q n h.losses)
      have hTT:0 < T n:=zero_lt_one.trans_le (pot_big Z D Q n h.losses)
      have htn:= h.delays n; let C':= max (‖A‖*K / ((t n)^w.val*T n)) (c' ((Y n).symm x) * ((t n)^u.val)/T n)
      filter_upwards [eventually_ge_atTop C'] with a ha
      constructor
      · exact (le_div_iff₀ (pow_pos htn u.val)).2 ((div_le_iff₀ hTT).mp ((le_max_right ..).trans ha))
      intro v; have he:= (norm_le_coins (b:=b) ho (begun Z n) (trimBelow w v))
      rw [at_trim L w ht hL]
      let u':=trimBelow w v
      have hvs:=coins_nonneg (b:=b) ho (zero_le_one.trans (begun Z n)) u'
      have hi:= (A.le_opNorm u').trans (mul_le_mul_of_nonneg_left he (norm_nonneg A))
      change ‖A u'‖ ≤ _*(T n * c' u')
      apply hi.trans
      rw [← mul_assoc]; have ht:= (div_le_iff₀ (mul_pos (pow_pos htn w.val) hTT)).mp ((le_max_left ..).trans ha)
      exact (mul_le_mul_of_nonneg_right ht hvs).trans_eq (by ring)
   have hf(n:ℕ) :∀ᶠ C:ℝ in atTop,N≤n→ c n → Clearance Z Y t g e D Q b x L w u n C:=by
       by_cases hi:N≤n ∧ c n
       · exact (cost n hi.1 hi.2).mono (fun _ he _ _=>he)
       exact Eventually.of_forall fun _ he h=> (hi ⟨he,h⟩).elim
   obtain ⟨C,hc,hh⟩:= ((eventually_ge_atTop (0:ℝ)).and ((Finset.range M').eventually_all.mpr (fun n _=> hf n))).exists
   refine ⟨C,hc,(eventually_ge_atTop N).mono ?_⟩
   have Hl(n:ℕ) : N ≤ n→ c n→ Clearance Z Y t g e D Q b x L w u n C:=by
     induction n using Nat.strong_induction_on with
     | h n IH=>
       intro hv hz; by_cases hn:n<M'
       · exact hh n (Finset.mem_range.mpr hn) hv hz
       have hp:max M N ≤ n-1:=by unfold M' at hn; omega
       cases n with
       | zero=> unfold M' at hn; omega
       | succ n=>
          have h0:N≤n:=(le_max_right ..).trans (by simpa using! hp)
          obtain ⟨h1,h3,h4,hV,hF⟩ := hM n (show _≤ n by omega)
          obtain ⟨h3,h2⟩:= h3 hz
          obtain ⟨hT,hA⟩:= hN _ hv hz
          by_cases hi:c n
          · obtain ⟨ha,hu⟩:=hN _ h0 hi
            exact relay x L w (h3 hi) (h.delays _) (h.delays _) h.losses hu hA hX hL ha hT hc (IH _ (Nat.lt_succ_self n) h0 hi) -- args order?
          obtain ⟨ha,hu⟩:=hN _ h1 hV
          exact relay x L w (h2 hi) (h.delays _) (h.delays _) h.losses hu hA hX hL ha hT hc (IH _ (Nat.lt_succ_of_le h4) h1 hV)
   intro n hn hx; exact Hl n hn hx
end YM.RG12.Alidade
