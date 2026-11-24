import YM.OPE.Loom.Ticket
/-!
# Cost of throwing into horizon d and propagating to a *fixed* stop.
Don't use this proof of logarithmic budget for a moving stop (new cell
packing supplies apply). Even for the root the seam must be placed at that
fixed stop. Leaves all constants from stops untouched. No precision strictly
beyond d claimed here. The historical price has a strictly additional power;
this allows errors in shifting geometry and in outputs fees from polynomial T.
-/
set_option autoImplicit false
noncomputable section
open Filter Function Set
open scoped Topology BigOperators
namespace YM.OPE.Loom
open Lattice RG Wilson MergeProof Accent Ribbons Source Overlay
open Bid ManyCopies PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow Bandage
open Push Marker
variable {G:Gauge} {C:Family G}{W r D}(L:Sharper C W r D)
local notation "Y" => C.path.levels
local notation "X" => C.path.levels.clock.hatBeta
local notation "δ" => renal C.path.levels
local notation "η" => near C.path.levels
local notation "ζ" => fly C.path.levels
local notation "Γ" => C.path.levels.params
set_option quotPrecheck false
variable {m : ℕ} (d K:ℕ)(hK:C.ref d ≤ K) {z v:ℝ}

def ebb (C : Family G) (d m : ℕ) (z : ℝ) := 4*(1+(C.path.levels.params m).columns)*(2*(C.S.a (m+1)^d*(C.path.levels.clock.hatBeta (m+1)*(4*(1/z)))))
-- conservative denominator substitute power^d instead of power^(d+1). b harmonic min.
def max1 (C:Family G)(d K m:ℕ)(z:ℝ):= renal C.path.levels m * (z/(16*C.path.levels.clock.hatBeta (m+1))) * (C.S.a K/C.S.a m)^d * (fly C.path.levels d K / fly C.path.levels d m)
def max2 (C:Family G)(d K m:ℕ)(z:ℝ):= fly C.path.levels d K / (64*(1+(C.path.levels.params m).columns)*‖alto C.path K d‖*ebb C d m z)
def bid (C:Family G)(d K m:ℕ)(z:ℝ):= ((max1 C d K m z)⁻¹+(max2 C d K m z)⁻¹)⁻¹
lemma ebb_pos (hp:0<z) : 0<ebb C d m z:= by unfold ebb; have hs:= C.S.a_pos (m+1); have he:= (Γ m).columns_ge; have h:= show 1 < X (m+1) from (Y).fits.delayed _; positivity
include L hK
lemma max1_pos (hp:0<z)(ht:K ≤ m) : 0 < max1 C d K m z:= by unfold max1; have hy:0 < X (m+1):= zero_lt_one.trans ((Y).fits.delayed _); have hx:0<δ m:= Real.rpow_pos_of_pos hy _; have hZ:= L.system.grows d m (hK.trans ht); have hQ:=L.system.grows d K hK; have he:= C.S.a_pos K; have hh:=C.S.a_pos m; positivity
lemma max2_pos (hp:0<z): 0 < max2 C d K m z:= by
   unfold max2; have hx:= L.system.grows d K hK; have hs := (Γ m).columns_ge; have h': 0<‖alto C.path K d‖:= by rw [alto_norm]; exact inv_pos.mpr (pow_pos (C.S.a_pos K) _)
   have hh:=ebb_pos d hp (C:=C) (m:=m); positivity
lemma prices (hp:0<z)(ht:K ≤ m) : let b:=bid C d K m z
      0<b ∧ march (fun _:Unit=>b) η K m () ≤ δ m*(z/(16*X (m+1))) ∧
       32*(1+(C.path.levels.params m).columns)*b*‖alto C.path K d‖*(ebb C d m z/gainChart C.path m K) ≤ ζ d K/2:=by
    intro b; let u:= max1 C d K m z; let v:=max2 C d K m z; have hu:0<u:=max1_pos L d K hK hp ht; have hv:0<v:=max2_pos L d K hK hp; have hc:0<b:= by change 0<(u⁻¹+v⁻¹)⁻¹; positivity
    have h₁: b≤u:=
      calc _ ≤ (u⁻¹)⁻¹ := inv_anti₀ (by positivity) (le_add_of_nonneg_right (by positivity:(0:ℝ) ≤ v⁻¹))
           _ = _ := by rw [inv_inv]
    have h₂: b≤v:= (inv_anti₀ (show 0<v⁻¹ by positivity) (le_add_of_nonneg_left (by positivity:(0:ℝ)≤u⁻¹))).trans_eq (inv_inv _)
    let x:= C.S.a m/C.S.a K; have hs:=C.S.a_pos K; have hy:= C.S.a_pos m; have hx:0<x:=by unfold x; positivity
    let f:ℝ:= 1+(Γ m).columns
    have hF:0<f:=by have := (Γ m).columns_ge; unfold f; positivity
    let T:= ‖alto C.path K d‖; have hT:0<T:=by unfold T; rw [alto_norm]; exact inv_pos.mpr (pow_pos (C.S.a_pos K) _)
    have hE:1≤gainChart C.path m K:= Real.one_le_exp (mul_nonneg (by norm_num) (sub_nonneg.mpr ((scale_mono C.S).monotone ht)))
    have hZ:0<ζ d K:=L.system.grows d K hK; have hm:0<ζ d m:= L.system.grows d m (hK.trans ht)
    have hh:= ebb_pos d hp (C:=C) (m:=m)
    refine ⟨hc,?_ ,?_⟩
    · have hp': x ≤ 1:= (div_le_one hs).mpr (C.S.strictAnti.antitone ht)
      apply le_trans (seeing C d L.system hc m K hK ht)
      have hz: b*x^(d+1) * (ζ d m/ζ d K) ≤ u*x^d*(ζ d m/ζ d K):= mul_le_mul_of_nonneg_right (mul_le_mul h₁ (pow_le_pow_of_le_one hx.le hp' (by omega)) (by positivity) hu.le) (by positivity)
      apply hz.trans_eq; unfold u x max1; rw [div_pow,div_pow]; field_simp
    apply le_trans (show 32*f*b*T*(ebb C d m z/gainChart C.path m K)≤ 32*f*v*T*ebb C d m z from ?_) (le_of_eq ?_)
    · apply mul_le_mul (by gcongr) (div_le_self hh.le hE) (div_nonneg hh.le (zero_le_one.trans hE)) (by positivity)
    unfold v max2; change 32*f*(ζ d K/(64*f*T*ebb C d m z))*T*_=_; field_simp; ring
variable {I : Type}{k j:I→ℕ}{f a c T:I→ℝ}{φ:Filter I}{b:ℝ} (hT:Tendsto T φ atTop) (h: Height C.S φ T k b) (ha:∀ᶠ i in φ,0<c i)(hh:Bill φ T (fun i=>(a i)⁻¹) c)
omit hK
include hT h hh
-- fixed-constant factors in some direction addressed by positivity from elsewhere
lemma ebb_cost : Bill φ T (fun i=>ebb C d (k i) (a i)) (fun i=> c i*C.S.a (k i)^d):= by
   let q i:= 1+(Γ i).columns; have hB:Cheap φ T (q ∘ k):= (Bill.const (1:ℝ) hT).add (columns_p hT L.toPackage.toTableTickets h).up hT
   have he := Bill.mul (shift_mesh hT h L.tabs |>.up.power hT d)
     (Cheap.times (hat_price hT (h.step (Y).fits.mesh)|>.up) (Cheap.times (Bill.const (4:ℝ) hT) hh))
   unfold ebb; simp_rw [one_div]; apply (Cheap.times (Cheap.mul (Bill.const (4:ℝ) hT) hB) (Cheap.times (Bill.const (2:ℝ) hT) he)).congr (EventuallyEq.refl _ _) (Eventually.of_forall fun i=>mul_comm _ _)
include ha hK
lemma bprice (hp:∀ᶠ i in φ,0<a i) : Bill φ T (fun i=>(bid C d K (k i) (a i))⁻¹) (fun i=> c i *C.S.a (k i)^d):= by
   let x := fun i=> X (k i+1); have he : Coins φ T x:= hat_price hT (h.step (Y).fits.mesh)
   let B i:=‖c i‖*‖C.S.a (k i)‖^d; let f i:= c i*C.S.a (k i)^d
   have hh₁ : Bill φ T (fun i=> (max1 C d K (k i) (a i))⁻¹) f:=by
      let v:= (C.S.a K)^d * ζ d K; have hv:0<v:= mul_pos (pow_pos (C.S.a_pos _) _) (L.system.grows d K hK); have hb:= (Y).fits.delayed
      have h0:= Cheap.mul (Cheap.div (Cheap.times (Bill.const (16:ℝ) hT) he.up) (renal_coins hT h)) (Cheap.div (fly_coins hT h d|>.up) (Bi.const v hv.ne' hT)); have hz:= Cheap.times h0 (Bill.mul hh (Bill.same φ T (fun i=>C.S.a (k i)^d))); apply hz.congr _ (EventuallyEq.refl ..); filter_upwards [ha,hp,h.grows.eventually_ge_atTop K] with i hc hy he
      change 16*x i / δ (k i)*(ζ d (k i)/v)*(_*_) = _; unfold max1 v x; rw [div_pow]; have ht:= C.S.a_pos (k i); have hs:=C.S.a_pos K; simp only [mul_inv_rev, inv_div]; ring
   have hh₂ : Bill φ T (fun i=> (max2 C d K (k i) (a i))⁻¹) f:=by
      let y := 64*‖alto C.path K d‖/ζ d K
      have ht:= (Bill.const (1:ℝ) hT).add (columns_p hT L.toPackage.toTableTickets h).up hT
      apply (Cheap.times (Cheap.mul (Bill.const y hT) ht) (ebb_cost L d hT h hh)).congr _ (EventuallyEq.refl ..)
      filter_upwards with i; unfold y max2; rw [inv_div]; ring
   simp_rw [bid, inv_inv]; exact hh₁.add hh₂ hT
end YM.OPE.Loom
