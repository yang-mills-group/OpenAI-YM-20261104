import YM.Contacts.Prairie.Share
namespace YM.Contacts.Prairie
open Function Set Finset Filter RG Wilson Lattice Precision Exterior Push.AbsoluteSums Extra.Iteration
open Bloch Milling Milling.Steam Pulse Spine MergeProof Milling.Forge Laurent Stationary Matrix Work.F08
open Milling.Garf Form House PertExtension.Series Tree Larch FreeResolvent PhysicalNext.RankCovariance
open Next.Free Milling.Lumen Barrage.Reserve
open scoped Topology BigOperators Matrix Classical NNReal ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {G: Gauge}
namespace Parcel
open Origin Barrage.Slope Ion Resetter
variable (e:Parcel G) (p q u:Word) (s:Step) (n:Side) {i j:ℕ} {ζ:ℝ≥0}{b:ℝ}
-- permission interval. Outgoing Ω only uses the (given) budget decay in this strip on input metrics; can shrink any further
abbrev A := Origin.stretch (e.flag s) e.K G (e.wheel p s).V
abbrev Cov := (e.wheel p s).V
structure ReelFee (x:ℝ): Prop where
   direct : (e.Cov p s).strip ζ x -- expose ζ via binder later
   feed : (e.A p s).strip ζ x
-- amplified difference in pricing. only asked on Lagoon enough
structure FineFee (x:ℝ): Prop where
   direct : (minusRows (e.Cov p s) (e.Cov q s)).strip ζ x
   flow : (minusRows (e.A p s) (e.A q s)).strip ζ x
structure License (S:Boom)(e: Parcel G)(ζ:ℝ≥0) : Prop where
   ok : enough e.Quota S
   light : 0<ζ
   lane : 4*ζ≤e.decade
   thin : 2*ζ≤1
   base (s:Step) (hs:s∈S): ∃ x≥(0:ℝ),∀ p, e.ReelFee p s x (ζ:=2*ζ)
   pairs (s:Step)(hs:s∈S): ∃ x≥(0:ℝ),∀ p q u,OK S u → e.FineFee (u++p) (u++q) s (x*mileage u) (ζ:=2*ζ)
variable {e} {S S':Boom}{η:ℝ≥0}
section
lemma ReelFee.fall (ht:ReelFee e p s (ζ:=η) b)(he:ζ ≤ η): ReelFee e p s (ζ:=ζ) b:= ⟨strip_mono ht.direct (by exact_mod_cast he) le_rfl,strip_mono ht.feed (by exact_mod_cast he) le_rfl⟩
lemma FineFee.fall (ht:FineFee e p q s (ζ:=η) b)(he:ζ ≤ η): FineFee e p q s (ζ:=ζ) b:= ⟨strip_mono ht.direct (by exact_mod_cast he) le_rfl,strip_mono ht.flow (by exact_mod_cast he) le_rfl⟩
lemma License.fall (ht: e.License S η)(he:0<ζ)(hx:ζ≤η):e.License S ζ:= by
   refine ⟨ht.ok,he,le_trans (by gcongr) ht.lane,le_trans (by gcongr) ht.thin, fun s hs=> ?_, fun s hs=>?_⟩; obtain ⟨a,ha,h⟩:=ht.base s hs; exact ⟨a,ha,fun p=> (h p).fall _ _ (by gcongr)⟩
   obtain ⟨a,ha,h⟩:=ht.pairs s hs; exact ⟨a,ha,fun p q u hu=> (h p q u hu).fall _ _ _ (by gcongr)⟩
lemma OK.restrict (h:S⊆ S') (he:OK S p): OK S' p := fun t ht=> h (he t ht)
lemma License.restrict (h:S⊆ S')(he:e.License S' ζ):e.License S ζ:= by
   refine ⟨fun s hs=>he.ok s (h hs),he.light,he.lane,he.thin,fun s hs=>he.base s (h hs),fun s hs=>?_⟩; obtain ⟨b,hb,hc⟩:=he.pairs s (h hs); exact ⟨b,hb,fun p q u hu=> hc p q u (OK.restrict _ h hu)⟩
-- independent s after L. Use common aperture through any finite allowed set
lemma leasible (hS:enough e.Quota S): ∃ ζ,e.License S ζ:= by
   -- original hS carries Q. Use common v but instantiate expenditure with S
   choose t v ht hv hB H using fun s:Step => wheel_bank G e.T (e.flag s) e.K e.J
   let d:= gate e.T e.J; let W:= insert d (S.image t); let hw: W.Nonempty:= ⟨d,by simp [W]⟩; let F:=W.min' hw; -- S.inf' -- maybe needs nonempty. rather insert default from d
     -- fill below (sed)

   have hD:0<d:= gate_pos ..; have hL:0<F:= by have hw: F=d ∨ ∃ s ∈ S,t s=F:= mem_insert.mp (min'_mem W hw) |>.imp_right fun h=> mem_image.mp h; rcases hw with h|⟨s,-,he⟩; exact h.symm ▸ hD; exact he ▸ ht s
   let σ:=min (F/4) (d/4); have hp:0<σ:= lt_min (by positivity) (by positivity)
   have he (s:Step)(h:s∈S): 2*σ ≤ t s:= by refine le_trans (b:=F) ?_ (Finset.min'_le W (t s) (Finset.mem_insert_of_mem (mem_image_of_mem t h))); rw [mul_comm, ← le_div_iff₀ (by positivity)]; exact (min_le_left ..).trans (div_le_div_of_nonneg_left hL.le (by positivity) (by norm_num))
   have hx (s:Step) (p:Word) := H s (e.eligible _) _ (e.toll p) (fun n=> ⟨e.symmetry _ _,(e.awake p s).gap n⟩) (e.wheel p s)
   have hw : 4*σ≤d:= by rw [mul_comm]; exact (le_div_iff₀ (by positivity)).1 (min_le_right ..)
   have hf : d ≤ 1 ∧ d ≤ e.decade:= by dsimp only [d,gate]; constructor; exact (div_le_self (by positivity) (by norm_num)).trans (min_le_left ..); exact (div_le_self (by positivity) (by norm_num)).trans ((min_le_right ..).trans (min_le_left ..))
   refine ⟨σ,hS,hp,hw.trans hf.2,(le_trans (by gcongr; norm_num) hw).trans hf.1,fun s hs=> ?_,fun s hs=>?_⟩; -- gcongr
   · exact ⟨_,zero_le_one.trans (hB _),fun p=> (ReelFee.fall (ζ:=2*σ) p s (⟨(hx s p).wheel,(hx s p).tilt⟩: ReelFee e p s (ζ:=t s) (v s)) (he s hs))⟩
   refine ⟨v s*e.shop,mul_nonneg (zero_le_one.trans (hB _)) e.gift_pos,fun p q u h=> ?_⟩; rw [mul_assoc]; apply FineFee.fall (u++p) (u++q) s (η:=t s) _ (he s hs); let Y:= t s; let w:=e.shop*mileage u; have hu (p q:Word) : (portfolio (e.column (u++p)).metric (e.column (u++q)).metric).strip Y w:= strip_mono (e.Q_strip p q u _ hS h) (NNReal.coe_le_coe.mpr ((hv _).trans hf.2)) le_rfl
   let V:= (hx s (u++q)).charge (e.wheel (u++p) s) (e.toll _) (fun n=> ⟨e.symmetry _ _,(e.awake _ s).gap n⟩) w (mul_nonneg e.gift_pos (mileage_pos _).le) (hu q p)
   exact ⟨V.1,V.2⟩
end
end Parcel
end
end YM.Contacts.Prairie
