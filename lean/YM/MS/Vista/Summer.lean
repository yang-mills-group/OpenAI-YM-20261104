import YM.MS.Vista.Leaf
/-!
# Uniform spectral phase bound on lifted corner sums.Absol via center lift. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Vista
open Set Filter Function Finset Metric MeasureTheory Real High
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Osc.Snap Native Lattice City Latch Job Belt Rake Flux Wire Book Convolve Orbit
open Rake.Geo Orbit.LogReal
open scoped Topology ContDiff Interval
variable {G:Gauge}{I E:Type}{M:Visa I}{P:Belt I}{L:I→ Side}{A:I→Cover}{ n:Side}
-- structural distance scaled sup and allowance
abbrev mine (n:Side)(x:Lattice.Site n): Prop:= n.val ≤ 16 * pdist x
lemma E_n (p:Lattice.Site n)(h:mine n p): (n.val:ℝ)≤16 * (pdist p:ℝ):= by exact_mod_cast h
lemma δ_side (x y:Half)(h:x≠y) : mine (periodN n) (thin n x-thin n y):= by
   rw [ ← map_sub (thin n) ]; unfold mine; rw [ show pdist (thin n (x-y))=( n.val) * pdist (x-y) from caress .., bornlf _ (sub_ne_zero.mpr h) ]; change 2*n.val ≤_; omega
lemma mine1 (k:Orbit.Zone n)(x:Half): mine (periodN n) (k+thin n x) = mine (periodN n) ( k-thin n x ):= by nth_rw 1 [ u_car n x ]; rw [sub_eq_add_neg]
lemma mine2 (k:Orbit.Zone n) (h:∀ z:Half,mine (periodN n) (k-thin n z)) : mine (periodN n) (k+k):= by
    unfold mine; rw [ altitude ]; let i:= (τ_frame n).parent k; obtain ht:= h i; unfold mine at ht; obtain he:= reduce (n:=n) k; rw [ Lattice.separation_comm,Lattice.separation ] at he; change pdist (k - thin n i) = _ at he; omega
lemma mine_op (x: Lattice.Site n) : mine n (-x)↔ mine n x:= by simp [mine]
lemma mine_sym (x y:Lattice.Site n): mine n (x-y) ↔ mine n (y-x):= by rw [← mine_op (x-y), neg_sub]
-- remote δ systems no metric.N:
abbrev Clearance (L:I→ Side)(A:Faces I): Prop:= ∀ i,∀ x:Half,mine (dimT L i) (wrap (dimT L i) ( A i )- thin (L i) x)
def Quota (L:I→Side)(A:I→Cover): Prop := ∃ C:ℝ, 0<C∧∀ i, ‖embed (A i)‖ ≤ C * ( L i |>.val:ℝ) -- syntax parser space
abbrev width (L:I→Side)(A:Faces I):= Quota ( dimT L ) A
lemma spanτ (x:Cover)(n:Side)(p:Axis) : Tone.bill ( Tone.embed x ) ( whole (ψstep n) ( Lattice.step p ))= Fiddle.bellZ ( Tone.embed (Gates ( wrap n x )) p * ψstep n ):= by
   have he:= Orbit.bill_walk (n:=n); rw [ ← η_walk ]; -- he: lambda metavar? h required
   rw [ he, ← wrap_lift (wrap n x), ← he _ (Gates _), η_walk ]; change bellZ ( pairing _ _ ) = bellZ ( _*_ ); rw [ Fiddle.atom, wrap_lift ] -- port sage
abbrev margin : ℝ:=tier/16
lemma mild : 0<margin:= by unfold margin; positivity
lemma gain_term (p:Lattice.Site n)(h:mine n p): ∃ x: Axis,margin ≤ |embed (Gates p) x*ψstep n| ∧ |embed (Gates p) x*ψstep n| ≤ tier-margin := by
   obtain ⟨i,hi⟩:=axis_max p; obtain H:= ψpp n ; obtain hv:= sizeX p; obtain hm : 2*(pdist p:ℝ) ≤ n.val:=(by exact_mod_cast hv); obtain hs:= E_n p h; obtain hz:= Bloch.side_pos n; obtain hT:= rising
   refine ⟨i,?_⟩; rw [abs_mul,abs_of_pos H, ← Real.norm_eq_abs, atτ,← hi]; unfold margin ψstep; rw [ ← mul_div_assoc ]; constructor; · apply (_root_.le_div_iff₀ hz).mpr; nlinarith
   apply (_root_.div_le_iff₀ hz).mpr; nlinarith
lemma phase_gain (h:∀ i, mine ( L i ) ( wrap ( L i ) ( A i ) )) : ∃ C:ℝ,0<C∧∀ i:I,∃ p:Axis, C≤ ‖(1:ℂ)- (be (A i) ( whole ( ψstep (L i) ) ( Lattice.step p )))⁻¹‖ := by obtain ⟨u,hu,hv⟩:= farBolt mild; refine ⟨ u,hu,fun i=>?_⟩; obtain ⟨p,hm⟩:= gain_term (wrap ( L i ) ( A i )) ( h i ); refine ⟨ p,?_⟩; unfold be; rw [spanτ,bill_absneg ]; exact hv _ hm.1 hm.2
lemma radar (S:Scale I)(H:∀ i,S.length i ≤ ( L i |>.val :ℝ ) )(h:∀ i, mine ( L i) ( wrap (L i) (A i))) : Radar S (fun i=> ( (L i).val:ℝ )) A (totalS ∘ L):= by
    obtain ⟨v,hv,hP⟩:= phase_gain h; choose P hp using hP; let b(i):= ψstep (L i); let T(i):=whole (b i) (Lattice.step ( P i )); have ht(i):0<b i:=ψpp _; have he(i): ‖T i‖≤ b i := ( sharp (P i) (b i) )|>.trans_eq (abs_of_pos (ht i)); intro E _ _ f x hF j; obtain hm:= f_cap (Γ:=L) H; obtain hx:= rapid_pay (T:=T) (μ:=totalS ∘ L) (S:=S) (U:=fun i=> be ( A i )) (fun i=> sailor _) hm.sector hF (fun i=>lounge (embed ( A i )) (T i)) (fun i=>( mul_le_mul_of_nonneg_left (he i) ( S.pos i|>.le))|>.trans (ν_engine H i)) rising.le (fun i=> Osc.Snap.boom ( ht i ) _ ) he v hv hp (hm.mint E) j;
    refine hx.raise ⟨ tier^j,pow_pos rising _,0,fun i p _=>?_ ⟩; simp only [pow_zero,mul_one]; rw [ show S.length i * b i=tier*(S.length i/(L i).val) from (by unfold b ψstep; ring),mul_pow ]; exact le_of_eq (by ring)
end YM.MS.Vista
