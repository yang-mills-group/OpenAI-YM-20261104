import YM.RGLocalTaylor.Retain.Stencil
/-!
# Texture - Price bill and telescoping for whole log moment
Use true angular V derivatives and joint moments inside the actual frame. Includes
Borel and locality (for pricing λ.AurE or λ.AurMark unchanged). Uses `ξ.mode`
not available on every x of arbitrary aperture, only earned moments. Need ALSO
recoverability for denormalized path continuation.Fire.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGLocalTaylor

open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F F' : Forest S.ratio} {P : Teller G}
variable {j n l k : ℕ} {R : Rep G f} {X : Coat T F} {η r q a Y W d C' A b s μ C v B : ℝ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable {H : Cash W s μ L Q o C T R}


open Blaze.March
open PhysicalNext PhysicalNext.Repeat Lotus Daisy Greenbelt
namespace Retain
open Mayer
namespace goodK

variable {M : ℕ} {Ξ : Utopia H j v d r C' χ}
   {θ ρ α γ e discount uJ vJ:ℝ} {w : Head S→ℝ} {u t: Stencils T M}
   {p z:Molecule S} (U : Decors z M)
   {N : Captain H j C' d v Y A b r B q n χ}
   {f' : Head S→ Insert T} {g : Head S→ℝ}
   (ha:Awning H N.conduit A b discount e uJ vJ k l)
   (hu: Priced N.conduit M w θ ρ α A u)(hq:Quoted N.conduit M w θ ρ α A γ u t)
   (he:∀ i∈p\z, EstFactor N.conduit i (f' i) A (g i) α) (hb:∀ i∈p\z,0≤g i)
   (hf:∀ i∈p\z, Fits H (f' i) (H.supportP i) j)
   (hp:Start p)(hV:z⊆p)(hy: troupe T R Q.halo (radiusB s) p)
   (ht: decorOrder U ≤ M)
local notation "Ξ'" => N.conduit
local notation "u'" => older p z g w
local notation "m'" => θ*ρ
local notation "F" => speedBill e uJ α j
local notation "Z" => (1+H.shapeW p)^(l+j)
local notation "k'" => (∏ i∈p, rateLeaf g w θ ρ U i)
local notation "D'" => (ρ^decorOrder U)⁻¹ * (F * u' * Z)
-- fit one receipt type. arities compressed AFTER integration, preserving all powers.
local notation "r'" => D' * ((2*(θ*ρ))^p.card)
variable {V: Config G c}
    (hh:(roster p).flags=∅)(hC : Healthy (Pressure.temp s) (H.unionP p) V)
variable (H) (p z)
-- meaning only when ≤M and Start p etc.
/-- genuine kernel-sector Taylor coefficient before coherently combining germs. Carries
unchanged operands `f'` (outside the V-exponential temperature class), for marking use.
-/
def validity (u:Stencils T M)(f':Head S→ Insert T)(n:ℕ) (V: Config G c):ℝ:= ∑ U∈ univ.filter (fun U:Decors z M=>decorOrder U=n),(parcel u p f' U).onLog H χ p V

variable {H p z}
lemma authentic (f':Head S→Insert T) (p z:Molecule S) : validity H p z (physical H M) f' (χ:=χ)= Mayer.coefficient p z H f' χ M:=rfl
include hu hb
lemma historical : 0≤ older p z g w:= mul_nonneg (prod_nonneg hb) (prod_nonneg fun _ _=>hu.nonneg _)
include ha
lemma printed (m:ℕ) : 0 ≤ (ρ^m)⁻¹ * (F*u'* Z):=by
   have ht:=historical hu hb
   have h:=ha.bSc; have hr:=ha.earn; have hW:=hu.scale; have hE:= H.positive_volume p; have hx:=hu.effort; unfold speedBill; positivity
include he hf hp hy hh hC ht hV
lemma volumeU : Ore V ((parcel u p f' U).onLog H χ p) v r' j:=by
   have hr:=ha.priced (covers_parcel U hu he hp hy ht) (prod_nonneg (ledger U hu hb)) hu.effort (fits_parcel U hu hp ht hf) hh V hC
   intro E _ _ _ X x ho hz; apply (hr E X x ho hz).climb _ le_rfl
   have hy:1≤ θ*ρ:= one_le_mul_of_one_le_of_one_le hu.value hu.scale
   rw [chance hp, Finset.card_empty,pow_zero,mul_one]; calc
    _ = D' * ((θ*ρ)^z.card) := by rw [fair_ledger _ hV]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left ((pow_le_pow_right₀ hy (card_le_card hV)).trans (pow_le_pow_left₀ (zero_le_one.trans hy) (le_mul_of_one_le_left (zero_le_one.trans hy) one_le_two) _)) (printed ha hu hb _)

omit hu
include hq
lemma feedbackU : Ore V ((parcel u p f' U).onLog H χ p-(parcel t p f' U).onLog H χ p) v (γ*r') j:=by
   have ht' := hq.gradeP; have hr:= ha.priced (devotes U he hp hy ht hq) (mul_nonneg (mul_nonneg hq.defect (Nat.cast_nonneg _)) (prod_nonneg (ledger U ht' hb))) ht'.effort (Fits.diffFits (fits_parcel U ht' hp ht hf) (fits_parcel U hq.gradeF hp ht hf)) hh V hC
   have hy:1≤ θ*ρ:= one_le_mul_of_one_le_of_one_le ht'.value ht'.scale
   intro E _ _ _ X x ho hz; apply (hr E X x ho hz|>.shimmy ((Fits.diffGerm (fits_parcel U ht' hp ht hf) (fits_parcel U hq.gradeF hp ht hf) hh hz (ho.symm ▸ hC) (Ξ:=N)).symm)).climb _ le_rfl
   rw [chance hp, Finset.card_empty,pow_zero,mul_one]; calc
    _ = γ*(D' * (p.card*(θ*ρ)^z.card)) := by rw [fair_ledger _ hV]; ring
    _ ≤ γ*(D' * ((2:ℝ)^p.card*(θ*ρ)^p.card)):= mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul (show (p.card:ℝ) ≤ (2:ℝ)^p.card by exact_mod_cast Nat.lt_two_pow_self.le) (pow_le_pow_right₀ hy (card_le_card hV)) (pow_nonneg (zero_le_one.trans hy) _) (by positivity)) (printed ha ht' hb _)) hq.defect
    _ = _:= by rw [mul_pow 2]

variable {d' :ℕ}(hn:d' ≤ M)
local notation "U₀" => (validity (χ:=χ) H p z u f' d')
local notation "U₁" => (validity (χ:=χ) H p z t f' d')
set_option quotPrecheck false
-- power of stencil radius gets caller conversion rates.
def creditStencil (M:ℕ)(θ ρ:ℝ):= (M+1:ℝ)*(2*(θ*ρ))
local notation "b'" => creditStencil M θ ρ
local notation "cash₀" => (ρ^d')⁻¹*(F*u'*Z)
local notation "paid'" => cash₀ * b'^p.card -- absorption size stamps.w_oC & markers. 
omit ht hq he
include hn hu
omit ha hb hy hh hC hV in
lemma identityBook : GaugeInvariant U₀ ∧ Measurable U₀ ∧ LocalOn (H.unionP p) U₀:= by
   let Y:=univ.filter (fun i: Decors z M=> decorOrder i=d'); let f(i:Decors z M):=(parcel u p f' i).onLog H χ p
   have hv i (hi:i∈Y):= Fits.log_seam (χ:=χ) (fits_parcel i hu hp ((mem_filter.mp hi).2.symm ▸ hn) hf)
   exact ⟨fun z V=> sum_congr rfl fun _ _=> Insert.onLog_invariant _ p z V, Finset.measurable_fun_sum _ (fun i (hi:i∈Y)=> (hv i hi).2),fun x y h => sum_congr rfl fun i hi=> (hv i hi).1 x y h⟩

-- pricing sum generic cost
omit ha hf hn hb hu hh hC hp hy
variable {V': Finset (Decors z M)} in
lemma cardRate : (V'.card:ℝ) ≤ (M+1:ℝ)^p.card:=by
   have h: V'.card ≤ (M+1)^z.card := (card_le_card (subset_univ V')).trans_eq (by simp [Decors]); exact_mod_cast (le_trans h (Nat.pow_le_pow_right (by omega : 0< M+1) (card_le_card hV)))
local notation "D!" => univ.filter (fun x:Decors z M=> decorOrder x=d')
local notation "A'" => cash₀ * ((2*(θ*ρ))^p.card)
include hu ha hb hy hh hf hC hp hn he
lemma printed_book : Ore V U₀ v paid' j:=by
   intro E _ _ _ X x ho hz; let f(U:Decors z M) t:=(parcel u p f' U).onLog H χ p (X t)
   have hf i (hi:i∈ D!):Brush j A' 1 (f i) x:= (mem_filter.mp hi).2 ▸ volumeU i ha hu he hb hf hp hV hy ((mem_filter.mp hi).2.symm ▸ hn) hh hC E X x ho hz -- dependent? Volume proof
   have ht:= (printed ha hu hb d'); have hv:=hu.scale; have hA:=hu.value
   apply (Brush.spree D! f (fun _=>A') zero_le_one hf).climb _ le_rfl
   rw [sum_const,nsmul_eq_mul]; apply (mul_le_mul_of_nonneg_right (cardRate hV) (mul_nonneg ht (by positivity))).trans_eq; unfold creditStencil; rw [mul_pow (M + 1:ℝ)]; ring
omit hu
include hq
lemma priced_ledger : Ore V (U₀-U₁) v (γ*paid') j:=by
   intro E _ _ _ X x ho hz; let f(u: Stencils T M)(U:Decors z M) y:=(parcel u p f' U).onLog H χ p (X y); let fD(i:Decors z M) y:= f u i y-f t i y
   have hF i (hi:i∈ D!): Brush j (γ*A') 1 (fD i) x:= (mem_filter.mp hi).2 ▸ feedbackU i ha hq he hb hf hp hV hy ((mem_filter.mp hi).2.symm ▸ hn) hh hC E X x ho hz
   have hu:= hq.gradeP; have ht:= printed ha hu hb d'; have hv:=hu.scale; have hA:=hu.value
   apply (Brush.spree D! fD (fun _=>γ*A') zero_le_one hF).shimmy (Eventually.of_forall (fun t=> (sum_sub_distrib (s:=D!) (f:=_) (g:=_)).symm)) |>.climb _ le_rfl -- direction
   rw [sum_const,nsmul_eq_mul]; apply (mul_le_mul_of_nonneg_right (cardRate hV) (mul_nonneg hq.defect (mul_nonneg ht (by positivity)))).trans_eq; unfold creditStencil; rw [mul_pow (M + 1:ℝ)]; ring
end goodK
end Retain
end YM.RGLocalTaylor
