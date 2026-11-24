import YM.RG12.Alidade.Office
import YM.RG12.Rail.Run
/-!
# Pay the offices on single lit levels of the Construction

`g` uses the exact same reflected sesqui and TRUE orientation, not necessarily real or positive;
proof compares at *geometrically scaled* nonredundant full flag, so by Gram legality a posteriori
states `Tests` in the currency realized. The all-letter Upper across rises consumes the
quantitative estimates of `LampR` even though they don't yet see the crucial cancellation.
The layout denominator is independently frozen eventually before all march starts. No
perturbative identities consumed in this Tier.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Alidade
open Function Set Filter Wilson Lattice RG Source Real Frames Commission Rail
open Function Filter Set Finset Lattice Wilson RG Next.Rank Next.Rank.Atlas Station Prayer Perch Glimmer
open Extraction Bid MergeProof Source Org Spec PhysicalNext PhysicalNext.RankCovariance PhysicalNext.InteractingRank.Soft
open MergeProof.East Arche Shapes Roof RG12.Frames RG12.Desk.Paired Pert.Dense
open PhysicalNext.Repeat.Legato.Bandage Next.Rank.Tapes.West
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{S:Table C.book}{f:Extraction.Order}{d:ℕ}
variable (U:Final C f S)
local notation "Z!"=> C.path.levels
-- lens denominators agree. Also arbitrary exis constructor choice Aga.
lemma lamp_torch (C:Family G)(N k:ℕ)(b:ℝ): lamp C N k (mag C.path.levels b k)= torchR C.path.levels b N k:=by
    unfold lamp torchR flareR ticks knot; push_cast; rw [mul_comm (↑N:ℝ)]
lemma sitespec {Y:Levels G}(h:G.Simple)(hs:Slugg Y){b:ℝ}(hb:0<b)(N₀:ℕ)(hN:0<N₀): let t:=torchR Y b N₀
    (∀ k,0 < t k)∧ ∀ᶠ k:ℕ in atTop,let x:=drift Y b N₀ k; x∈Set.Icc 1 2 ∧ t (k+1) ≤ t k∧ Y.S.a k ≤ t k ∧ t k ≤ Y.S.a k*2*mag Y b k:=by
   intro t
   refine ⟨flare_pos Y b N₀ hN,?_⟩
   have h := tour_clock Y h b hb hs N₀ hN 2 1 (by norm_num)
   have ht : ∀ᶠ k:ℕ in atTop, drift Y b N₀ k ≤ 2:=by
      have he: Tendsto (fun k:ℕ=>k-1) atTop atTop:= tendsto_atTop_atTop.mpr (fun j=>⟨j+1,by intros; omega⟩)
      filter_upwards [he.eventually h,eventually_ge_atTop 1] with k hk hi
      exact (by simpa only [Nat.sub_add_cancel hi] using! hk.2.2.2.2)
   filter_upwards [h,ht] with k hx hk q
   let n:= mag Y b k; let δ:=jumped Y b N₀ (knot N₀ n) k
   have hδ: drift Y b N₀ (k+1)*(t k/t (k+1))=δ := across_torch b N₀ k hN
   have hv:1 ≤ q:= hx.1.1
   have he:0<t (k+1):=flare_pos _ _ _ hN _
   have hu:1 ≤ t k/t (k+1):=by
      have hi : 0<t k:= flare_pos _ _ _ hN k
      have hp:=hx.2.1.1
      change 2 ≤ δ at hp; have h₁:= hx.2.2.2.2; nlinarith only [hδ,hp,h₁,mul_le_mul_of_nonneg_right h₁ (div_pos hi he).le]
   refine ⟨⟨hv,hk⟩,(one_le_div he).mp hu,?_,?_⟩
   all_goals have hg: t k=Y.S.a k * (mag Y b k) * q:= by unfold q drift atR t torchR flareR; field_simp [(mag_pos Y b k).ne']
             rw [hg]
   · apply le_trans _ (le_mul_of_one_le_right (mul_nonneg (Y.S.a_pos k).le (mag_pos ..).le) hv)
     rw [mag_bill]; exact le_mul_of_one_le_right (Y.S.a_pos k).le (Glimmer.costed b _ hb.le)
   convert mul_le_mul_of_nonneg_left hk (mul_nonneg (Y.S.a_pos k).le (mag_pos Y b k).le) using 1 <;> first | rfl | ring

variable {lit:ℕ→Prop}(P:Port C)(hP:Outbound P lit U.room.cutoff) -- need lit binder!
-- physical g RF cost at literal length
abbrev lens (U:Final C f S)(d:ℕ)(ax:Axis)(N₀:ℕ)(t:ℝ):S.Field d→ℝ:= Real.sqrt ∘ (sampleForm U (Shapes.scope ax N₀) d t).eval
abbrev wheelR (U:Final C f S)(d:ℕ):= Desk.Sector U.sector.derivatives d
set_option quotPrecheck false
local notation:max "XX"=>wheelR U d
local notation:max "TT!"=>U.sector.derivatives
local notation:max "bell"=>Cells.standard C
lemma pad (ax:Axis) (d:ℕ):∃ K:ℝ,1≤K ∧ ∀ᶠ N:ℕ in atTop,∀ (i:Grade d),∀ s:ℝ,s∈Set.Icc 1 2→∀ v:C.label i,
    (polished C.labels i i ax (N:ℝ)⁻¹ s ((Cells.standard C).project i v) ((Cells.standard C).project i v)).re ≤ K*mass C i v^2:=by
   let L(i:Grade d):= LinearMap.toContinuousLinearMap ((bell).project i)
   choose! c K hc hK hp using fun i:Grade d=> worthwhile C.labels i ax (P:=2) (by norm_num)
   let B(i):ℝ:=K i *‖L i‖^2; let J:=1+∑i,B i; have he₁(i):0≤B i:=by unfold B; exact mul_nonneg (zero_le_one.trans (hK i)) (sq_nonneg _) -- gcongr?
   have he:0 ≤ ∑i,B i:=sum_nonneg (fun i _=>he₁ _)
   refine ⟨J,by unfold J;linarith,?_⟩
   filter_upwards [eventually_all.mpr hp] with N hn i s hs v
   apply (hn i s hs _).2.trans
   have hL: ‖(bell).project i v‖ ≤ ‖L i‖*mass C i v:=by
      exact ((L i).le_opNorm _).trans (mul_le_mul_of_nonneg_left (norm_le_mass ..) (norm_nonneg _))
   calc
    _ ≤ K i*(‖L i‖*mass C i v)^2:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hL 2) (zero_le_one.trans (hK i))
    _ ≤ _:=by rw [mul_pow,← mul_assoc]; exact mul_le_mul_of_nonneg_right ((single_le_sum (s:=univ) (fun i _=>he₁ i) (mem_univ i)).trans (by unfold J; linarith)) (sq_nonneg (mass C i v))
-- power & prices variables, posed actual
variable {φ:Filter UVIndex}[φ.NeBot]{M:∀ d,ℕ→RepChart C d}
variable {W:Bid.Worth}{u ψ β δ:ℕ→ℝ}{r:ℕ→ℕ} {L:∀ N p m:ℕ,m<N→MergeProof.GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable (h:G.Simple)(hp:Scrim C W u ψ β δ (fly C.path.levels) r L)
variable (i:Fin 3)
local notation "arc!"=> (P.panels d i).arc
variable (hQ:Observing C U.room.cutoff φ M)(hb:φ ≤ f.fuse)
include U hP hQ hb h hp
lemma shines (ax:Axis): ∀ N:ℕ,0 < N→ ∀ᶠ k:ℕ in atTop,
    let n:=trays d; let T:=P.panels d;let a:=arc!; let b:=P.budget d
    let s:=drift (Z!) a N k;let t:=torchR (Z!) a N k
    ∀ (Z:TableL C d),Good (ϕ:=φ) (n:=n) T P.chart U.room.cutoff P.haar P.locality b i Z k→
      Roof.CastH U d ax N 1 t s M k Z:=by
   intro N hN
   let n:=trays d; let T:=P.panels d;let a:= (T i).arc
   obtain ⟨c,hc,H'⟩:= lightR (l:=(Ultrafilter.of φ:Filter UVIndex)) T P.chart U.room.cutoff h hp P.haar P.locality _ (hP.covered.2.1 d) i U hQ hb ax N hN (n:=n) (Nat.le_add_left _ _)
   have ha:0<a:=by have ht:=(T i).huge; linarith only [ht,Nat.cast_nonneg (α:=ℝ) d]
   have hd:= tour_clock (Z!) h _ ha hP.speed N hN n d (Nat.le_add_left _ _)
   have hw:Tendsto (fun k=>c*Ship.budget (Z!) n k) atTop (nhds 0):=by simpa using (Ship.diminishes (Z!) n h (by unfold n trays; omega)).const_mul c
   filter_upwards [H',hd,hw.eventually (ge_mem_nhds zero_lt_one)] with k hk he hj n' T' a' b s t q hs x y v w
   obtain ⟨U₀,hU,hV⟩:=hs.pages
   apply (@hk U₀ hU q hV (knot N (mag (Z!) a k)) he.1 x y v w).trans
   exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hj (mass_nonneg ..)) (mass_nonneg ..)

-- express all-letter occupancy on U rise. derive using comparison, then relative norm vs lamp
lemma cover (ax:Axis):∃ K:ℝ,1≤K∧∀ᶠ N:ℕ in atTop,∀ᶠ k:ℕ in atTop,let t:=torchR (Z!) arc! N k
    ∀ (q:TableL C d), Good (ϕ:=φ) (n:=trays d) (P.panels d) P.chart U.room.cutoff P.haar P.locality (P.budget d) i q k→
      ∀ (j:Grade d)(v:C.label j), lens U d ax N t ((TT!).rise j.is_le (engineering (S:=S) M j k v)) ≤ K*mass C j v :=by
   obtain ⟨K,hK,ht⟩:= pad (C:=C) ax d
   let z:ℝ:= 2^d*(3/2:ℝ); have hz': 1 ≤ (2^d:ℝ):=one_le_pow₀ (by norm_num); have hz : 1≤z:=by unfold z; linarith
   refine ⟨(K+1)*z,one_le_mul_of_one_le_of_one_le (by linarith only [hK]) hz,?_⟩
   have he : 0 < arc! :=by have ht := (P.panels d i).huge; linarith only [ht,Nat.cast_nonneg (α:=ℝ) d]
   filter_upwards [ht,eventually_gt_atTop 0] with N ht hN
   filter_upwards [shines U P hP h hp i hQ hb ax N hN,(sitespec (Y:=(Z!)) h hP.speed he N hN).2] with k hk hj t q hq j v -- args
   obtain ⟨W,hM,hL⟩:=hq.pages
   obtain ⟨y,rfl⟩:=(produced hL j).2 v
   let s:= drift (Z!) arc! N k
   have he' := hk q hq j j y y
   have hu:0 < t:= (sitespec h hP.speed he N hN).1 k
   let x:= glowH (S:=S) M k (q j) y
   have hX: x= engineering (S:=S) M j k (q j y):=by change S.project _ ((_ : ℂ) • M j k _) = ((_ : ℂ) • S.project _ (M j k _)); rw [map_smul]
   let p:= (sampleForm U (Shapes.scope ax N) d t).eval ((TT!).rise j.is_le x)
   have hf:p ≤ (K+1)*mass C j y^2:=by
      let μ := illumination S U.room.kernel.spin j j ax N t x x
      have hμ: p=μ.re:=by
         have h':= counted U ax d ((TT!).rise j.is_le x) N 1 t
         rw [Nat.cast_one,mul_one] at h'
         simp only [Arche.here,mul_one] at h'
         apply h'.trans; exact congr_arg Complex.re (Roof.lifts d U.room.kernel.spin _ _ _ _ _ hu _ _ (TT!) U.room.kernel.laws.toSymmetric U.phase.transport.injection U.phase.transport.rights j.is_le j.is_le)
      rw [hμ]; let w:=polished C.labels j j ax (N:ℝ)⁻¹ s ((bell).project j y) ((bell).project j y)
      have hh : μ.re - w.re ≤ (mass C j y)^2 := (le_abs_self _).trans ((Complex.abs_re_le_norm (μ-w)).trans (by change ‖μ-w‖ ≤ 1 * mass C j y * mass C j y at he'; simpa [sq] using he'))
      linarith only [hh,ht _ _ hj.1 y]
   have he :mass C j y ≤ z*mass C j (q j y):=
      (hL.base j y).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) j.is_le) (show 0≤(3/2:ℝ) by positivity)) (mass_nonneg ..))
   have h₁: 1 ≤ K+1:= by linarith only [hK]
   have hP:=mass_nonneg C j (q j y)
   rw [←hX]
   change Real.sqrt p ≤ _
   have hsq:p ≤ ((K+1)*z*mass C j (q j y))^2:=by
      apply hf.trans; simp only [mul_pow]; rw [mul_assoc]; exact mul_le_mul (le_self_pow₀ h₁ (by norm_num)) (by rw [← mul_pow];exact pow_le_pow_left₀ (mass_nonneg ..) he 2) (sq_nonneg _) (sq_nonneg _)
   exact (Real.sqrt_le_sqrt hsq).trans_eq (Real.sqrt_sq (mul_nonneg (mul_nonneg (zero_le_one.trans h₁) (zero_le_one.trans hz)) hP))
end YM.RG12.Alidade
