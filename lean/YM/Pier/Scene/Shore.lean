import YM.Pier.Scene.Lengths
/-! Sample genuine separated shapes over the native clock. All introduced
positions in the resulting envelopes retain the price and occupancy of the
panoramic allScenes estimate (≥ B^8, ≤ hatBeta^exponent, bounded aspect).
Quantify *all allowed lattice placements approximating shape here*, not just
the simultaneously provided exemplary ones. Exact ``snap within`` has
size ~(ℕ stamp)^(-(n+const)) relative. We don't approximate continuum
correlations by snapping positions on this strength alone. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG17.Panoramic
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Marker Source Overlay
open FullVolume.Sever MergeProof MergeProof.Accent Extra.Histories Extra.Trajectories Extra.Multi Next.Rank Edition Spindle SharpGram Trace RG12 Next.UVStress
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Bandage
open OPE OPE.Yarn Ribbons Ribbons.ManyCopies Ribbons.ManyCopies.Patrol PertExtension Extraction
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}(R:Run G) {n:ℕ}
local notation "H"=> R.family.path.levels.clock.hatBeta
local notation "C"=> R.family
local notation "A"=> R.family.path.levels
local notation "a"=> R.family.S.a
local notation "S!"=> R.family.S
set_option quotPrecheck false
variable {T0:Campaign R}{W:Campaign.Pillars R T0} {h:G.Simple}(U:Pier.Starter R h T0 W)

abbrev tick (R:Run G) (r:ℝ)(t k:ℕ) := Nat.floor (r/(t:ℝ)/(4*R.family.S.a k))

/-- diameter-bound encoded by absolute coordinates at 0. Translation on
    lattice can be used separately (use the all-scenes estimates before this one).
    Not changing offsets/parity by asserting a continuum identification.
    For convenience use Euclidean distances throughout; no conversion from
    `Scaling.window` needed to apply. -/
def AtShore (t:ℕ)(X:Points n) := (∀ i, ‖X i‖ ≤ t) ∧ ∀ i j,i≠j → (t:ℝ)⁻¹ ≤ ‖X i-X j‖
variable {k s m t p :ℕ}{r:ℝ}{X:Points n} (hp:1≤t) (hX:AtShore t X)(hr:0<r)
    (hx: EnvelopeRange R m k t s r)

def Neighbor (X:Points n) (r:ℝ)(t':ℝ)(x : Fin n→ Site (R.family.side k p)) :=
  ∀ i, ‖(S!).place (x i) - r • X i‖ ≤ t'

local notation "µ" => tick R r t k
private lemma admSize (z:ℕ) : (1/2:ℝ) ≤ (S!).radius z:=
  div_le_div_of_nonneg_right (mod_cast (C|>.S.period z).property) (by norm_num)

include hX hp hx hr
lemma fitsSnap (x:Fin n→ Site (R.family.side k p))
    (hv : Neighbor R X r (r/(t:ℝ)/4) x) :
      (∀ i j,separation (x i) (x j) ≤ (32*t^2)*µ) ∧
      (∀ i j,i≠j → µ ≤ separation (x i) (x j)) ∧
      (µ:ℝ) ≤ H k^(s+29) := by
   let z(i:Fin n) := (C).S.place (x i); let w:ℝ:=t; have hw:1≤w:=by unfold w; exact_mod_cast hp
   let dotQ(i:Fin n):= r • X i; let B:= r/w
   have hp': 0<w:= zero_lt_one.trans_le hw
   have hγ:0 < (a k):= (S!).a_pos _
   have hD: 0<B:= div_pos hr hp'; have h1:B ≤ r:= div_le_self hr.le hw
   have hU: r ≤ r*w := le_mul_of_one_le_right hr.le hw
   let L := r/w/(4*a k)
   have hf {i} : ‖z i-dotQ i‖ ≤ B/4:= hv i
   have hV(i): ‖dotQ i‖ ≤ r*w:= by unfold dotQ; rw [norm_smul,Real.norm_of_nonneg hr.le]; exact mul_le_mul_of_nonneg_left (hX.1 _) hr.le
   have he(i j:Fin n) : ‖z i-z j‖ ≤ r*4*w:= by
      have eq : z i-z j=(z i-dotQ i)+(dotQ i-dotQ j)-(z j-dotQ j):= by abel
      rw [eq]; apply ((norm_sub_le ..).trans (add_le_add ((norm_add_le ..).trans (add_le_add hf ((norm_sub_le ..).trans (add_le_add (hV _) (hV _))))) hf)).trans
      nlinarith only [h1,hU,hr]
   have hsep(i j:Fin n)(h : i≠j): r/w/2 ≤ ‖z i-z j‖:= by
      have eq : dotQ i-dotQ j=(dotQ i-z i)+(z i-z j)+(z j-dotQ j):= by abel
      have hR:r/w ≤ ‖dotQ i-dotQ j‖ := by
        unfold dotQ; rw [← smul_sub,norm_smul,Real.norm_of_nonneg hr.le]
        exact le_trans (le_of_eq (div_eq_mul_inv ..)) (mul_le_mul_of_nonneg_left (hX.2 _ _ h) hr.le)
      have hz: B ≤ (B/4+ ‖z i-z j‖)+B/4:= by
        rw [eq] at hR; exact hR.trans ((norm_add_le ..).trans (add_le_add
          ((norm_add_le ..).trans (add_le_add (by rw [norm_sub_rev]; exact hf) le_rfl)) hf))
      unfold B at *; linarith only [hz]
   have h(i j:Fin n):= RG17.nativeShort C (x:=x i) (y:=x j) (lt_of_le_of_lt (he i j) ((lt_of_lt_of_le hx.radius (admSize R p))))
   have hl:1 ≤ L := hx.lots
   have hB : (1:ℝ) ≤ µ:= by exact_mod_cast (show 1 ≤ µ from (pow_pos ((A).budget k).B_pos (8:ℕ)).trans_le hx.extra)
   have hy:L ≤ 2 * (µ:ℝ):= by
      have hx:L < (µ:ℝ)+1:= Nat.lt_floor_add_one _; linarith only [hx,hB]
   have hz:(µ:ℝ) ≤ L:=Nat.floor_le (le_trans zero_le_one hl)
   refine ⟨fun i j => ?_,fun i j h'=>?_,?_⟩
   · apply Nat.cast_le (α:=ℝ) |>.mp; push_cast; apply le_of_mul_le_mul_left _ hγ
     apply ((h i j).1.trans (he i j)).trans
     have hg: r/w ≤ (2*(µ:ℝ))*(4*a k):= (div_le_iff₀ (show 0 < 4*(a k) by positivity)).mp hy
     have hM:= mul_le_mul_of_nonneg_right ((div_le_iff₀ hp').mp hg) (show 0≤4*w by positivity)
     change _ ≤ (a k)* (32*w^2 * _); linarith only [hM] -- ring_nf?
   · apply Nat.cast_le (α:=ℝ) |>.mp; change (µ:ℝ) ≤ (separation (x i) (x j):ℝ)
     have hm:= (le_div_iff₀ (show 0 < 4*a k by positivity)).mp hz
     have hg:= le_trans (hsep i j h') (h i j).2
     apply le_of_mul_le_mul_left _ hγ; linarith only [hm,hg]
   apply hz.trans; apply le_trans _ hx.far; apply div_le_div₀ hr.le h1 hγ (by linarith only [hγ])

include hx
lemma ferry : ∀ p:ℕ, ∃ x:Fin n→ Site (R.family.side k p), Neighbor R X r ((4*n:ℝ)*a k) x := by
   intro p; let t':= r • X
   have ht(i:Fin n)(j:Axis): |t' i j| < (C).S.radius p := by
      have hb : |t' i j| ≤ ‖t' i‖:= PiLp.norm_apply_le (t' i) j
      refine hb.trans_lt (lt_of_le_of_lt ?_ (lt_of_lt_of_le hx.radius (admSize R p)))
      change ‖r • X i‖ ≤ _; rw [norm_smul,Real.norm_of_nonneg hr.le]; refine (mul_le_mul_of_nonneg_left (hX.1 _) hr.le).trans ?_; gcongr; linarith only [hr]
   have hf:t'∈ Fund (C).S p n:=fun i j=>let H₁:= abs_lt.mp (ht i j); ⟨H₁.1,H₁.2.le⟩
   obtain ⟨x,hx',hp⟩:= Extraction.corners (N:=k) hf
   have he: address (a k) t'= fun i=> lift (x i):= hx'
   have hx := approximate ((C).S.a_pos k) t'; rw [he] at hx
   rw [dist_eq_norm] at hx
   refine ⟨x,fun i=>?_⟩; apply le_trans ?_ hx; exact PiLp.norm_apply_le (tag (a k) (fun i=> lift (x i))-t') i

omit hX
open Spec
variable {f:Extraction.Order}{S:Table R.family.book}{F:Spec.Final R.family f S} (L:Layout F) (hL: Located L) (hZ : Comparably R L.level)
include hL hZ
omit hx hr
include U
lemma relative_round (n:ℕ) (s:ℕ) : ∀ᶠ r:ℝ in home,
    let m:= L.level r
    let k:= berth R (s+25) m
    (4*n:ℝ)*a k ≤ r/(H m)^s ∧ (4*n:ℝ)*a k ≤ r/(t:ℝ)/4 := by
   filter_upwards [planning R U L hL hZ s t hp, (Station.hat_rate (A) h|>.comp hL.level.growing).eventually_ge_atTop (16*(n:ℝ)*t)] with r hx hf m k
   have he: 16*(n:ℝ)*(t:ℝ) ≤ H m:= hf
   let u:= H m
   have hπ:1≤u:= ((A).fits.delayed _).le
   have ht:0<a k:= (C).S.a_pos _; have hφ := (C).S.a_pos m
   have hy: u^(s+25)*a k ≤ r:= (le_div_iff₀ ht).mp hx.space
   have hp₁ : (1:ℝ)≤ t:= by exact_mod_cast hp
   have hg: u*a k ≤ r:= (mul_le_mul_of_nonneg_right (show u ≤ u^(s+25) by simpa only [pow_one] using (pow_le_pow_right₀ hπ (show 1≤ s+25 by omega))) ht.le).trans hy
   refine ⟨(le_div_iff₀ (show 0<u^s by exact pow_pos (zero_lt_one.trans_le hπ) _)).mpr ?_,?_⟩
   · have h0 : 4*(n:ℝ)≤ u := (show 4*(n:ℝ) ≤ 16*(n:ℝ)*t from by nlinarith only [Nat.cast_nonneg (α:=ℝ) n,mul_le_mul_of_nonneg_left hp₁ (Nat.cast_nonneg n)]).trans he
     have hq := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
       (h0.trans (show u ≤ u^25 by simpa only [pow_one] using pow_le_pow_right₀ hπ (show 1≤ 25 by decide))) ht.le)
         (show 0 ≤ u^s from pow_nonneg (zero_le_one.trans hπ) _)
     apply le_trans hq; apply le_trans (le_of_eq (show u^25*a k*u^s=_ from ?_)) hy; rw [pow_add]; ring
   rw [le_div_iff₀ (by norm_num : (0:ℝ)<4),le_div_iff₀ (by linarith only [hp₁] : 0<(t:ℝ))]
   nlinarith only [hg,mul_le_mul_of_nonneg_right he ht.le]
end YM.RG17.Panoramic
