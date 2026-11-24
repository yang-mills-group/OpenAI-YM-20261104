import YM.SharpGram.Annulus.Rolls

/-!
# True annulus price at all log-length times (conditional)

Local Schur price suffices; projection & one-clock shear are already paid.
`Checkout.Late` and `intermediates` paid in Full; allocate base costs and
iterate. Explicit iteration with engineering powers and one extra log allowance
per lower-grade conversion, only through announced horizon. No smoothing of
neighbor length or assumption of continuity is needed for interim points.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SharpGram.Annulus
open Function Set Filter MeasureTheory Analysis Extraction Table Ward Climb RG Lattice
open Org Spec Next.UVStress Lenses Push.FiniteDetection.Free Weak.Portfolio
open scoped Topology ContDiff BigOperators Classical
set_option quotPrecheck false
variable {G:Gauge}{C:Family G}{S:Table C.book}{f:Extraction.Order}{u:Filter (ℕ×ℕ)}
variable {F: Final C f S}
local notation "P"=> C.path.levels.clock.hatBeta
local notation "V!"=>F.sector.derivatives
local notation "σ"=>F.room.kernel.spin
variable {d w i j : ℕ}
local instance (d : ℕ) : FiniteDimensional ℝ (S.Field d) := Module.Finite.trans ℂ _

-- fixed-L logical adjoints reading. Before choosing any test-dependent terminal.
lemma certifies (L : S.Field d →ₗ[ℂ] ℂ) (n : ℕ) (he : Valid F d n) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ x, ‖L x‖ ≤ K * life F n x := by
  obtain ⟨δ,h,ht⟩:= SharpGram.margin _ he
  let b := (LinearMap.toContinuousLinearMap L)
  let c := (Real.sqrt δ)⁻¹
  refine ⟨‖b‖ * c,mul_nonneg (norm_nonneg b) (inv_pos.mpr (Real.sqrt_pos.2 h)).le,fun x=>?_⟩
  have hh := ht x
  have hx : ‖x‖ ≤ c * life F n x := by
    apply (le_inv_mul_iff₀' (Real.sqrt_pos.2 h)).2
    apply (sq_le_sq₀ (by positivity) (positiveLife (F:=F) _ _)).mp
    rw [mul_pow,Real.sq_sqrt h.le,life,Real.sq_sqrt (positive F.room.kernel (Real.exp_pos _) _)]
    rw [mul_comm _ δ]; exact hh
  calc
    _ ≤ _ := b.le_opNorm x
    _ ≤ _ := (mul_le_mul_of_nonneg_left hx (norm_nonneg b)).trans_eq ((mul_assoc ..).symm)

lemma baseReceipt (L : S.Field d →ₗ[ℂ] ℂ) (hw:w≤d) (hL : Kills (C:=C) (V!) hw L) (n : ℕ) (ht : ∀ e:ℕ,e ≤ d→ Valid F e n) :
    ∃ K : ℝ, 0≤K ∧ ∀ x, ‖L x‖ ≤ K * book F w n d x := by
  have hb :=dial_pos n
  induction d with
  | zero=> obtain rfl:= Nat.eq_zero_of_le_zero hw; simpa only [book,↓reduceIte] using certifies L n (ht 0 le_rfl)
  | succ d ih=>
    obtain ⟨K,hK,HK⟩:=certifies L n (ht _ le_rfl)
    let T:=(V!).rise (Nat.le_succ d)
    rcases Nat.eq_or_lt_of_le hw with hw|hw
    · subst w; refine ⟨K,hK,fun x=>?_⟩
      have hx:L x=L (cap F d n x):=by
        nth_rw 1 [recombine (n:=n) F x]; rw [map_add,liftA,LinearMap.restrictScalars_apply,hL d (Nat.lt_succ_self d),zero_add] -- may fail with lift
      rw [hx]; rw [book,if_pos le_rfl,bookLower _ (Nat.lt_succ_self d),mul_zero,add_zero]; exact HK _
    have hw':w≤d:=by omega
    let M := L.comp T
    have H : Kills (C:=C) (V!) hw' M:=by
      intro e he x
      change L ((V!).rise _ _) = _
      rw [(V!).transit F.room.kernel.laws.toSymmetric F.phase.transport.injection]; exact hL e he x
    obtain ⟨b,hb',hT⟩:=ih M hw' H (fun i hi=>ht i (by omega))
    let c:=max K (b*dial n); refine ⟨c,hK.trans (le_max_left ..),fun x=>?_⟩
    let y:= floorAt F d n x; let z:=cap F d n x
    have he':L x=M y+L z:= (congr_arg _ (recombine (n:=n) F x)).trans (map_add ..)
    rw [he',book,if_pos (Nat.le_of_lt hw)]
    apply (norm_add_le ..).trans
    calc
       _ ≤ b * book F w n d y + K*charge F n x := add_le_add (hT y) (HK z)
       _ ≤ c * (dial n)⁻¹ * book F w n d y + c * charge F n x:=add_le_add
           (mul_le_mul_of_nonneg_right (by unfold c; rw [←div_eq_mul_inv, le_div_iff₀ hb]; exact le_max_right ..) (bookPos ..))
           (mul_le_mul_of_nonneg_right (le_max_left ..) (positiveCharge _ _))
       _ = c*(charge F n x+(dial n)⁻¹ * book F w n d y):=by ring

/-- telescope EXACT charges; no constants in the ratio. -/
lemma teleport (x:S.Field d) (k n : ℕ) (h : k≤n)
    (he : ∀ a, k ≤ a → book F w (a+1) d x ≤ epoch ^ d * precision a^i* book F w a d x)
    (hp : ∀ a, k ≤ a → book F w a d x ≤ epoch⁻¹ ^ w * precision a^j * book F w (a+1) d x) :
    book F w n d x ≤ (plank k / plank n)^d * (dial n / dial k)^i * book F w k d x ∧
    book F w k d x ≤ (plank n / plank k)^w*(dial n / dial k)^j * book F w n d x:= by
  let r := book F w
  have hu:0<plank k:=Real.exp_pos _
  have hk:= dial_pos k
  have hE := zero_lt_one.trans epoch_ge
  induction n, h using Nat.le_induction with
  | base=> simp [hu.ne',hk.ne']
  | succ n h ih=>
    have hn:0<plank n:=Real.exp_pos _
    have hl:0<dial n:=dial_pos n
    have hd:0<precision n := zero_lt_one.trans_le (baseDial n)
    have hs:=dial_pos (n+1)
    have hec: plank (n+1)= plank n / epoch := by rw [plank_power, pow_succ,← plank_power]; rfl -- div defin
    refine ⟨(he n h).trans ((mul_le_mul_of_nonneg_left ih.1 (by positivity)).trans_eq ?_ ), ih.2.trans ((mul_le_mul_of_nonneg_left (hp n h) (by positivity)).trans_eq ?_)⟩
    · rw [hec,precision]; simp only [div_pow]; field_simp
    rw [hec,precision]; simp only [div_pow,inv_pow]; field_simp

section Iterate
variable (h : Fits F) (B : Mantle F u)
include B h
/-- uniform function at integer log length -> arbitrary radius in interval. K unit log-cost power. -/
lemma inbound (d : ℕ) (x:S.Field d) : ∃ i:ℕ, ∃ H:ℝ, 0≤H ∧ ∀ᶠ n:ℕ in atTop, life F n x ≤ H * dial n^i / plank n^d:=by
   obtain ⟨i,j,hi⟩:=intermediates h B d 0 (Nat.zero_le d)
   obtain ⟨k,hk⟩:=eventually_atTop.mp hi
   let K:=plank k^d * book F 0 k d x / dial k^i
   have hb : 0≤K:=by unfold K; apply div_nonneg (mul_nonneg (pow_pos (Real.exp_pos _) _|>.le) (bookPos ..)) (pow_pos (dial_pos _) _|>.le)
   refine ⟨d+i,K,hb,?_⟩; filter_upwards [eventually_ge_atTop k] with n hn
   have hT:=teleport x k n hn (fun a he=>(hk a he x).1) (fun a he=>(hk a he x).2)
   have hP:0<plank n:=Real.exp_pos _; have hd':=dial_pos n; have hk':=dial_pos k
   apply (bookOrigin F n d x).trans
   exact (mul_le_mul_of_nonneg_left hT.1 (pow_pos hd' _|>.le)).trans_eq (by unfold K; rw [pow_add]; simp only [div_pow]; field_simp)

lemma outbound (w : ℕ)(hw : w ≤ d)(L : S.Field d →ₗ[ℂ] ℂ)(hL : Kills (C:=C) (V!) hw L) :
    ∃ j : ℕ, ∃ H : ℝ, 0 ≤ H ∧ ∀ᶠ n : ℕ in atTop, ∀ x, ‖L x‖ ≤ H * dial n^j * plank n^w * life F n x:=by
   obtain ⟨i,j,he⟩:=intermediates h B d w hw
   obtain ⟨k,hk⟩:=eventually_atTop.mp (he.and (atSmall B d))
   obtain ⟨u,hU,hA⟩:= baseReceipt L hw hL k (hk _ le_rfl|>.2)
   let K:=u*dial d / (plank k^w * dial k^j)
   have hP : 0 < plank k := Real.exp_pos _; have he:=dial_pos d; have hh:=dial_pos k
   have hK : 0≤K := by unfold K; positivity
   refine ⟨j,K,hK,?_⟩; filter_upwards [eventually_ge_atTop k] with n hn x
   have ht : 0<plank n:=Real.exp_pos _; have hd :=dial_pos n
   have h := teleport (w:=w) x k n hn (fun a hx=>(hk a hx).1 x|>.1) (fun a hx=>(hk a hx).1 x|>.2)
   have hT := h.2.trans (mul_le_mul_of_nonneg_left (budgeted F w n d (hk _ hn|>.2) x) (by positivity))
   refine ((hA x).trans (mul_le_mul_of_nonneg_left hT hU)).trans_eq ?_
   change u*((plank n / plank k)^w * (dial n / dial k)^j * (dial d * life F n x)) = _
   unfold K; simp only [div_pow]; field_simp
end Iterate
end YM.SharpGram.Annulus
