import YM.OPE.Mountains.Costs
import YM.OPE.Mountains.Arrange
/-!
# Step in any orientation and at the exact joint log weight

A single redaction can be priced even when adjacent scales still
have super-logarithmic fading (including having the same relative exp rate).
Not because we insert a formal abstraction for a tree-product, but by
joint sub-pattern pricing, insertion from the actual Wilson sign terms, and
unselected spectra of the underlying hierarchy. The context outside the parent may
indeed have leaves that are arbitrarily more expensive than the entire subtree
being redacted. These statements expect tickets from the actual construction
for Matrix (including upper *and* lower costs); they do not assume any OPE
bounds or separated multiplication bounds over forests.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Mountain
open Function Filter Finset OPE.Log Trunk Reels Log.Trunk.Shuttle Portrait
open scoped Classical Topology BigOperators ContDiff
set_option quotPrecheck false
variable {G:Gauge}{C:Family G}{F: Extraction.Order}{S:Table C.book}(U:Spec.Final C F S)
    {P:Prescription U.sector.derivatives} (hP:P.Coherent)
variable (H:Services C F S) {φ:Filter (ℕ×ℕ)} [φ.NeBot] (hf:φ ≤ F.fuse)
    {W r D}(V:LogPackage C W r D) (hG:MatrixTicket (C:=C) S U.sector.derivatives φ)
variable {I J:Type}[Fintype I] {s:Arboreal I} {χ:Ultrafilter J} {t:I→ℝ} {x:J→I→ E4}{R:J→I→ℝ}{M δ:ℝ}{i j k o:I} {a b : Finset I} (p:I→ C.book.Token) (d:ℕ) (w:Mode U.sector.derivatives)
variable (h:s.Coterie (χ:Filter J) t M δ x R) (ht:s.Active a) (ha:b⊆ s.live a) (hy:i∈ s.middle a)
local notation "T!"=> (fun i=>s.fullLife (R i))
-- law scope allows call away shift
include V H hf hP hG h ht
lemma localFee (ho:o∈a)(hu:b⊆s.inputs a o): Wallet (χ: Filter J) T! (fun j=> s.fee p (R j) b o w.fst • coalesce P b (x j) p o w):=by
    have hq:= h.keep; let S':=s.tower o; have hz:= ht.included ho
    by_cases hb:b=∅
    · letI : IsEmpty (↑b:Type):=⟨fun u=> notMem_empty u.val (hb ▸ u.property)⟩; simp_rw [coalesce,empty_coeff P _ _ _ U.room.kernel]; rcases Nat.eq_zero_or_pos w.fst with hh|hh
      · have hp (i:J): s.fee p (R i) b o w.fst=1:= by rw [hh,hb]; simp [fee,rent]; -- name
        simp_rw [hp,one_smul]; exact Wallet.const h.time _
      simp_rw [Prescription.highVan U.room.kernel.laws.toSymmetric U.phase.transport.injection hP w hh,smul_zero]; exact Wallet.const h.time (0:ℂ)
    obtain ⟨r,hr⟩:= nonempty_iff_ne_empty.mpr hb; obtain ⟨Z⟩:= paints h hz; let k : (↑b:Type):=⟨r,hr⟩; have he : ∀ i∈ b, s.Anc o (s.parent i):= fun i hi=> inside ht ho (hu hi); let Q:= Portrait.frame h Z k he
    let a':= Z.hue o; let m:=2*costCap s*M; let η:=δ/2; have hm : 0 ≤ m:= cap h; have ha:b ⊆ s.live a:= fun j hj=> halfSpace (hu hj) -- binder j implicit issue
    have hw₀ := mura h Z ht ha k he (tower_at.mpr ⟨hz,Anc.same s o⟩) ((mem_filter.mp (hu hr)).2); have hZ:= Portrait.mark h Z hz; have hw:a' = 0:= hZ; let X j:= crop (x j) b; let p':= crop p b; let Y j:= OPE.away (X j) (x j o)
    let u(j:J):= Payments.priceSet Q univ p' (Z.top j) / (Z.top j 0)^w.fst; let W' j:= s.fee p (R j) b o w.fst
    have hp : Wallet (χ:Filter J) T! (fun j=> u j • P.ope w (Y j) p' 0):= Reels.direct U (H:=a') (M:=m) (η:=η) (Q:=Q) (r:=Z.low) (X:=Y) (show a' ≤ Q.age Q.star from hw ▸ Nat.zero_le _) hm (half_pos hq) hw₀ p' w hf H V hG hP (z:=fun _=>(0:E4)) Z.schedule ((Z.schedule.ahead (Nat.zero_le _)).pos.mono (fun j hj=> by rw [norm_zero]; exact mul_nonneg hj.le hm))
    apply ((tag p w.fst h Z k he hz).up.smul hp).congr; filter_upwards [Portrait.positive p w.fst h Z k he] with j hj; change (W' j/u j:ℝ) • _= _; rw [← mul_smul,div_mul_cancel₀ _ (show u j≠0 from hj.ne')]; congr 1; change P.ope w (Y j) _ 0=P.ope w _ _ _; exact (by simpa only [sub_self] using ope_away P p' (X j) (x j o) (x j o) w)
lemma throughout : Wallet (χ: Filter J) T! (fun j=> s.fee p (R j) (s.live a) s.root w.fst • coalesce P (s.live a) (x j) p s.root w):= localFee U hP H hf V hG p w h ht ht.main (by rw [s.top_roots])
include hy
local notation "B!"=> (s.alter P a p x i d (fun j b p=> coalesce P (s.live b) (x j) p s.root w))
local notation "u!"=> (fun j=> s.fee p (R j) (s.live a) s.root w.fst)
lemma estimate_term (q:Mode U.sector.derivatives) : Wallet (χ:Filter J) T! (fun j=> u! j • (coalesce P (s.inputs a i) (x j) p i q * coalesce P (s.live (s.redact a i)) (x j) (update p i (P.letter q)) s.root w)):=by
    exact (by simpa only [mul_one] using (multiply_cash (W:=fun _=>(1:ℝ)) p w.fst h ht hy (P.letter q) (localFee (b:=s.inputs a i) U hP H hf V hG p q h ht (mem_erase.mp hy).2 (Subset.refl ..)) (F':=fun j=> coalesce P (s.live (s.redact a i)) (x j) (update p i (P.letter q)) s.root w) (by simpa only [mul_one] using throughout U hP H hf V hG _ w h (redacted ht hy)))) -- ξ arrow type congr mul Fee F
lemma roughish : Wallet (χ:Filter J) T! (fun j=> u! j • B! j):=by
    unfold alter; simp_rw [smul_sub,smul_sum]; exact (throughout U hP H hf V hG p w h ht).sub h.time (Wallet.sum h.time fun q _=>estimate_term U hP H hf V hG p w h ht hy q)
variable (he:s.Border a i)
local notation "q!"=> (fun j=> R j (s.parent i)/R j i)
include he
-- F forced f packageV.Root.Mark.Cluster_support
lemma diminish (Z:Portrait s χ R s.root) (hz:Z.hue (s.parent i)<Z.hue i) (hU:(s.inputs a i).Nonempty) : Wallet (χ:Filter J) T! (fun j=> (u! j*(q! j)^(d+1)) • B! j):=by
    let v:=s.live a; obtain ⟨u,hu⟩:= hU; let r:(↑v:Type):=⟨u,halfSpace hu⟩; let b:=s.live a; have hr:∀ j∈v,s.Anc s.root (s.parent j):= fun j _=> s.closure _; have hx:= (mem_erase.mp hy).2; have hV:=ht.included hx
    let Q:=frame h Z r hr; let X j:= crop (x j) v; let p':= crop p v; let k':=s.root; let η:=δ/2; let m:=2*costCap s*M; let n:=Z.hue i; let l:=Z.hue (s.parent i); let q:=Q.focus n; let z j:= x j k' - x j i; let y j:= OPE.away (X j) (x j i)
    let M₁ j:= Payments.priceSet Q univ p' (Z.top j); let M₂ j:= Payments.fuel (Z.top j) n l (d+1); let D j:= (Z.top j 0)^w.fst;
    let M' j:= M₁ j /D j; let g j:= Q.gap j r; let F j:= P.ope w (y j) p' (z j); let E j:= Reels.paidStep P w p' q (y j) (z j) d; have hm:= cap h; have ht':s.live a ⊆ s.live a:= Subset.refl _; have h₁ : Q.Strike n l:= selected h Z ht ht' r hr hx he (s.closure _) hu hz
    have Hx := mura h Z ht ht' r hr (tower_at.mpr ⟨hV,s.closure i⟩) (show s.Anc i u from (mem_filter.mp hu).2)
    have hZ:∀ᶠ i in χ,‖z i‖ ≤ Z.top i 0 *m:=by
       have hp:= Portrait.reach h Z (tower_at.mpr ⟨s.initial,Anc.same ..⟩) (s.closure i); let o:=s.root; rw [Portrait.mark h Z s.initial] at hp; filter_upwards [hp] with j hj; unfold z; rw [norm_sub_rev, mul_comm]; exact hj
    have hs : Wallet (χ: Filter J) T! (fun j=> (M₁ j*M₂ j /D j) • (F j-E j)):= Reels.plenary U (P':=V) Z.schedule h₁ hm (half_pos h.keep) p' hZ w hf H hG hP Hx -- arg order
    apply ((tag p w.fst h Z r hr s.initial).up.mul (Portrait.value (d+1) h Z i hV (s.closure _)).up|>.smul hs).congr -- grouping
    have hv': ∀ᶠ j in χ,0<M₂ j:=by filter_upwards [(Z.schedule.ahead h₁.atMost).pos,(Z.schedule.ahead (hz.le.trans h₁.atMost)).pos] with j hj he using pow_pos (div_pos he hj) (d+1)
    filter_upwards [Portrait.positive p w.fst h Z r hr,hv'] with j hj hp; rw [offering U P p d w ht hy (Portrait.mainOffer h Z ht ht' r hr hx (s.closure _) hu hz)]; change ((u! j /M' j * ((q! j)^(d+1)/M₂ j):ℝ)) • ((M₁ j*M₂ j / D j) • (F j-E j))= _ • (coalesce _ _ _ _ _ _ - E j); rw [← mul_smul,show M₁ j*M₂ j / D j= M' j * M₂ j by unfold M'; ring,show F j= coalesce P v (x j) p k' w from ope_away P p' (X j) (x j s.root) (x j i) w]; congr 1; have hp':0<M' j:= hj; change _ * (M' j* M₂ j)=_; field_simp -- rew binder V v defeq

lemma upon_border : Wallet (χ: Filter J) T! (fun j=> (u! j*(q! j)^(d+1)) • B! j):=by
    by_cases hp:s.inputs a i=∅
    · apply (Wallet.const h.time (0:ℂ)).congr; filter_upwards [unit_repair (x:=x) U P p d w ht hy h hp hP] with j hj; rw [hj,smul_zero]
    obtain ⟨Z⟩:=paints h s.initial
    rcases lt_or_ge (Z.hue (s.parent i)) (Z.hue i) with hz|hz; · exact diminish U hP H hf V hG p d w h ht hy he Z hz (nonempty_iff_ne_empty.mpr hp)
    have hZ : Wallet (χ:Filter J) T! q! := Portrait.budget h Z (tower_at.mpr ⟨ht.included (mem_erase.mp hy).2,s.closure i⟩) (tower_at.mpr ⟨s.inward i,s.closure _⟩) hz -- orientation
    apply ((hZ.pow h.time (d+1)).smul (roughish U hP H hf V hG p d w h ht hy)).congr; filter_upwards with i; rw [← mul_smul, mul_comm]; -- i shadows root
end YM.OPE.Arboreal.Mountain
