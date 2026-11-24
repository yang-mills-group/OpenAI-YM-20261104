import YM.AllOrder.Ink.Spectrum
import YM.AllOrder.Ink.Drill
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Ink
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace.SigmaP Ker
open Progress.ClassicalKin Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response
open scoped BigOperators Topology Classical ContDiff
variable {n m:Side} {α β : Type} [Fintype α] [Fintype β] {k N M:ℕ} {a C D b:ℝ}
namespace Echo
open Money Pointwise Further.PhysicalPeriodLimitF933 Shingle Macrame
local notation "B" => Field
local notation "X[" n "]"=> rule α n
section commute
variable (W:Macrame.Window n m M)
omit [Fintype α] in
lemma rever (u:X[n])(i:Site m)(v:Point α): convey W u (stood i v) = u (stood (W.cut i) v):= by change u ( W.cut _,_) =_; unfold stood; rw [W.port]; rfl
omit [Fintype α] in
lemma voice (u:X[n])(x:Site m)(S : Slip (Point α)): invoice x S (convey W u)=invoice (W.cut x) S u:= by induction S with
 | nil=> rfl
 | cons i S ih=> rw [invoice_cons,invoice_cons, Pi.mul_apply,Pi.mul_apply]; exact congr_arg₂ (·*·) (rever ..) ih
omit [Fintype α] in
lemma pay (G : Field α)(x:X[n]): G.table m (convey W x)= (M:ℝ)*G.table n x:= by
 have hs(u:Site m):G.site m u (convey W x)=G.site n (W.cut u) x := tsum_congr fun j=> congr_arg (G.fee j*·) (voice W x u (G.slip j)); rw [Field.table_apply,Field.table_apply]; simp_rw [hs]; rw [show ∑ i:Site m,G.site n (W.cut i) x= _ from multiplied _ W.fold (fun i=>G.site n i x), nsmul_eq_mul]
lemma amounts (u:X[n]): ‖convey W u‖ ≤ ‖u‖:= (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i=> norm_le_pi_norm u (BookM W α i)
end commute
section infinity
variable {D': Side→ℝ}{g: ℕ→Side}{σ:ℝ}
def Pulsed (C:Side→ℝ):Prop:= ∃ c : ℝ, ∃ k : ℕ, 0≤c ∧ ∀ i, 0≤C i∧ C i ≤ c*(i.val:ℝ)^k
lemma scaleLean {V:Type}{Λ:V→ℝ}{f :V→Side→ℝ}(h:Pay Λ f)(v:V):Pulsed (f v):= by obtain ⟨F,hf,k,h⟩:=h; exact ⟨F v,k,hf.nonneg v,h v⟩
open Asymptotics
lemma crest (h:Pulsed D')(ha:Tendsto (fun i=> (g i).val) atTop atTop)(hf:0<a): Tendsto (fun i=>D' (g i)*dearth a (g i)) atTop (𝓝 0):= by
 obtain ⟨c,k,hc,h⟩:=h; let S (i:ℕ):ℝ:= (g i).val; have ht : Tendsto (fun i=> S i^k * dearth a (g i)) atTop (𝓝 0):= by
    have he : Tendsto (fun i:ℝ=> i^k/Real.exp (a*i)) atTop (𝓝 0):= (isLittleO_pow_exp_pos_mul_atTop k hf).tendsto_div_nhds_zero; unfold dearth; simp only [neg_mul,Real.exp_neg, ← div_eq_mul_inv]; exact he.comp (tendsto_natCast_atTop_atTop.comp ha)
 refine squeeze_zero (fun i=> mul_nonneg (h (g i)).1 (Real.exp_pos _).le) (fun i=> (mul_le_mul_of_nonneg_right (h (g i)).2 (Real.exp_pos _).le).trans_eq (show (c*((g i).val:ℝ)^k)*Real.exp (-a*(g i).val)=c*(S i^k*dearth a (g i)) from mul_assoc ..)) ?_; simpa using Tendsto.const_mul c ht -- application syntax
variable {F: Bills α}{G:Field α}{Ad:Side→ Prop}
local notation "X"=> rule α n
variable {t:ℕ→ℕ}(W:∀ i, Macrame.Window n (g i) (t i))
lemma transported (he:Pert Ad F G a C D' k)(hp:Pulsed D')(ha:Tendsto (fun i => (g i).val) atTop atTop)(hf:0<a) (hg:Often Ad) (hs:∀ i,0<t i)(χ:(rule α n→ℝ)→ℝ)(hχ:LinTest _ k χ):
   Tendsto (fun i=>χ ((↑(t i):ℝ)⁻¹ • (F (g i) ∘ convey (W i)))) atTop (𝓝 (χ (G.table n))) := by
 let U i : X→ℝ:= ((↑(t i):ℝ)⁻¹) • (F (g i) ∘ convey (W i)); let D(i:ℕ):= U i-G.table n
 rcases hg with ⟨b,h'⟩; have hu : ∀ᶠ i in atTop, Ad (g i):=(ha.eventually (eventually_ge_atTop b)).mono (fun i h=>h' _ h); have hD(i) : D i= (↑(t i):ℝ)⁻¹ • ((F (g i)-G.table (g i))∘ convey (W i)):= by ext1 x; change (↑(t i):ℝ)⁻¹ * F _ _ - _=_ * (_-G.table _ (convey _ _)); rw [pay, mul_sub,inv_mul_cancel_left₀ (by exact_mod_cast (hs i).ne')]
 have hx(n:Side):=(he.1.binding hf.le (n:=n)).2.1; apply station_rank hχ (hx _)
 · filter_upwards [hu] with i hi; change Rank X k (U i); rw [show U i=D i+G.table n from (sub_add_cancel ..).symm, hD]; exact Rank.add (Rank.scal (Rank.lead (he.2 _ hi).2.1 _) _) (hx _)
 intro x; have hb := crest hp ha hf; let C0 i:= D' (g i)*dearth a (g i); have hl : Tendsto (fun i=>D i x) atTop (𝓝 0):= by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr; refine squeeze_zero' (Eventually.of_forall fun i=>norm_nonneg _) ?_ (show Tendsto (fun i=>C0 i * roi x ^ k) atTop (𝓝 0) from (by simpa using hb.mul_const (roi x ^ k))); filter_upwards [hu] with i hi;
    let Λ:= (↑(t i):ℝ); have hL:(1:ℝ)≤Λ:=by unfold Λ; exact_mod_cast (show 1≤t i from hs i)
    rw [hD i,Pi.smul_apply,norm_smul]; refine (mul_le_of_le_one_left (norm_nonneg _) (show ‖Λ⁻¹‖ ≤ 1 from ?_)).trans ?_
    · rw [Real.norm_of_nonneg (by positivity)]; exact inv_le_one_of_one_le₀ hL
    refine ((he.2 _ hi).2.2 _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ k) (he.2 _ hi).1); exact add_le_add le_rfl (amounts (W i) _)
 have h': Tendsto (fun i=> D i x+G.table n x) atTop (𝓝 (G.table n x)):= by simpa only [zero_add] using hl.add (tendsto_const_nhds (x:=G.table n x))
 refine h'.congr (fun i=>?_); change U i x-G.table n x+_= _; rw [sub_add_cancel]
end infinity
end Echo
end YM.AllOrder.Ink
