import YM.LocalLTE.Fan.Salt
/-! Finite allocated monomial. No references to H invoice in actual piece. Subdensity Brush. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Fan.Bakers
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6 ConnectedActivityE6.Blaze Blaze.March Captain Mask Raw Matter Frond Coat Vine
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Gate Scroll Vine Tablet Metric Poll Flux Shield Pond Raw
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
open Brush Foramen Pastel
variable {v z r W w s t y η γ B a μ: ℝ} {j n m N M : ℕ} {Q: YM.ConnectedActivityE6.Target G P}{o: Target.Order G W}{R:Rep G f}
variable (X:Coat T F)(R:Rep G f)
local notation "K"=> Veil c f
local notation "E"=>Disk G c
variable (D:Finset (Veil c f))
abbrev LevelsΛ (k:ℕ):= ↥D→ Fin k
def lilies (w:K→ℝ)(c:LevelsΛ D N):= ∏ i:↥D, ask (w i.val) (c i)
lemma fixture (f:K→ℝ)(n:ℕ): (∏ i∈D,Bakers.afloat n (f i)) = ∑ z:LevelsΛ D n,lilies D f z:=by
   rw [← Finset.prod_coe_sort D (fun i=>afloat n (f i))
   ]; unfold lilies; simp_rw [afloat, Finset.prod_univ_sum,Fintype.piFinset_univ]
def tones (w:K→ℝ)(z:LevelsΛ D N):= ∑ i:↥D,w i.val * ((z i).val+1:ℕ)
def pact (w:K→ℝ)(z:LevelsΛ D N):= ∏ i:↥D,w i.val^((z i).val+1)
lemma paid (w:K→ℝ)(h:∀ i∈ D,0≤w i)(hh:∀ i∈ D,w i≤1)(z:LevelsΛ D N):0≤ pact D w z ∧ pact D w z≤ ∏ i∈ D,w i:=by
  unfold pact; have hv (i:↥D):0≤ w i.val ^ ((z i).val+1):=pow_nonneg (h i.val i.2) _
  refine ⟨prod_nonneg fun i _=>hv i,?_⟩
  rw [← prod_coe_sort D w]; apply prod_le_prod (fun i _=>hv i)
  intro i _; exact pow_le_pow_of_le_one (h i.val i.2) (hh i.val i.2) (Nat.succ_le_succ (Nat.zero_le (z i).val)) |>.trans_eq (pow_one _)
lemma pastel (w v:K→ℝ)(hB:0<B) (z:LevelsΛ D N): pact D (fun i=>w i*B^v i) z=pact D w z*B^(tones D v z):= by
   unfold pact tones; simp only [mul_pow, prod_mul_distrib]; congr 1
   rw [Real.rpow_sum_of_pos hB]; apply Finset.prod_congr rfl; intro i _; rw [Real.rpow_mul hB.le]; exact (Real.rpow_natCast _ _).symm
lemma valueL (w v:K→ℝ)(h:∀ i∈ D,|v i|≤w i)(z:LevelsΛ D N): |lilies D v z| ≤ pact D w z:= by
  unfold lilies pact; rw [abs_prod]; refine prod_le_prod (fun _ _=>abs_nonneg _) fun i _=>?_ ; unfold ask; rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ ((Nat.factorial _ :ℕ):ℝ)⁻¹),abs_pow]; exact le_trans (mul_le_of_le_one_left (pow_nonneg (abs_nonneg _) _) (inv_le_one_of_one_le₀ (by exact_mod_cast Nat.factorial_pos _))) (pow_le_pow_left₀ (abs_nonneg _) (h i.val i.2) _)

variable (Θ:ChartRatio G)(s:ℝ)(I:Finset (Tubular f G))
def songP (x:E)(z:Body (↥I))(p:LevelsΛ D N) := pledgeΛ X I z (Vine.pass x)* lilies D (coming Θ R X x (Pond.spill I z)) p
def curlP (x:E) (p:LevelsΛ D N):= ∫ z in cabinet I s, Bakers.songP X R D Θ I x z p ∂Fan.pool I X 0
lemma monies (p:E) : Fan.pool I X p=Poll.sweep (planeQ X I (Vine.pass p)):= rfl
lemma brushL {w:E→ K→ℝ}{x:E}{u:K→ℝ}(hp:∀ i∈D, Brush j (u i) 1 (fun x=>w x i) x) (p:LevelsΛ D N) :
    Brush j (pact D u p) ((D.card:ℝ)*(N:ℝ)) (fun x=> lilies D (w x) p) x:=by
   let v (i:↥D):=(p i).val+1
   have hx {r:ℝ}(f:E→ℝ) (hf:Brush j r 1 f x) (n:ℕ): Brush j (r^n) (↑n) (fun p=> (f p)^n) x:= by
      induction n with
      | zero=> simp only [pow_zero,Nat.cast_zero]; simpa only [norm_one] using! (Brush.certified (k:=j) (x:=x) (le_refl (0:ℝ)) (1:ℝ))
      | succ n ih=> push_cast; simp_rw [pow_succ]; exact ih.paints hf
   have he (i:↥D): Brush j ((u i)^v i) (↑N) (fun x=>ask (w x i.val) (p i)) x:=by
     have hs:= hx _ (hp i i.2) (v i); let Z:ℝ:= (Nat.factorial (v i):ℕ); have hZ:1≤ Z:=by unfold Z; exact_mod_cast Nat.factorial_pos _
     exact ((hs.smul Z⁻¹).climb (by rw [Real.norm_of_nonneg (by positivity : 0≤ Z⁻¹)]; exact mul_le_of_le_one_left hs.nonneg (inv_le_one_of_one_le₀ hZ)) (by exact_mod_cast (show v i≤N from (p i).2))) -- edit
   simpa only [sum_const,nsmul_eq_mul,card_univ,Fintype.card_coe] using! Brush.all_prod (univ:Finset (↥D)) _ _ _ (fun i _=> he i)
end YM.LocalLTE.Fan.Bakers
