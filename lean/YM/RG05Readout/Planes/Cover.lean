import YM.RG05Readout.Chalice.Choir
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Planes
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories Cells Overlay
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper Motion
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station Ribbons
open Records Basket Halls Shadow Flatten
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {i n m p N d:ℕ}
    {b k l:ℕ}{Q:ℝ}(h:C.Makes){D: Address.Rail C}{B:ℕ→ℕ→ℝ}
set_option quotPrecheck false
open Pulse Extraction Extraction.Lease
open Push.RelayDifference
variable {D:Address.Rail C}

variable {f: Extraction.Order}

/-! A transcription at common origin: affordable → vetted literal against calibrated matrices, absorb a finite bank then same at ALL higher SBP orders on-demand. For low-weight planes repaint them further. -/
open Bay Chalice
/-!
# Plane transport for ACTUAL engraved array on threshold fields.
 Never use capacities of beam attributes alone: those may be charged at next index and unlimited versus L_i. At any actual Spine retrieve EXACT budgets at b- through hm using authenticated S, same map from density valuation. Then never replenish Adj except on OF.G ν.Intermediate PM.
-/
local notation "χ"=> C.path.levels
local notation "w₀"=> ld C.path.levels m
local notation "Λ"=> C.S.block m
local notation "X1"=> Palette C d
variable {U:Sight C d p}{V: Address.Emblems C d} (hw:Awake D B b d)(hP:Spine D B h b p d N U V)
local notation "A"=> B d m
abbrev powerFare (B:ℕ→ℕ→ℝ)(d m:ℕ):= 4*max 1 (B d m)
local notation "A!"=> powerFare B d m
abbrev tolerance (C:Family G)(m:ℕ):= trim (C.S.block m)+ld C.path.levels m * Doors.rate (C.S.block m) -- name imports?
lemma exists_letter : Nonempty (Beam 0) := by
    let B:Body:= Nuclear.core E4 1
    let Q:↥(Native.Orb 0):= records 0 0 B
    have he: Q≠0:= by
       intro ht; have hx:= congr_arg Subtype.val ht; have ht : Tensor.coeff B.val 0 0 (fun _=>0)= (0:ℂ):= congr_arg (fun x:Tensor.T E4 ℂ 0=> x (fun _=>0)) hx; simp only [Tensor.coeff, iteratedFDeriv_zero_apply, _root_.smul_apply] at ht; norm_num [B,Nuclear.core] at ht
    haveI : Nontrivial (Native.Orb 0):= ⟨⟨Q,0,he⟩⟩
    exact ⟨⟨0,Module.finrank_pos⟩⟩
include h hw hP
lemma adhered (hb:b≤ m) (ht:m < N) : (∃ (t s r:ℝ), 0≤ r∧r ≤ tolerance C m∧ Contour C m d t s r (V m).toLinearMap) ∧ ∀ x:X1,size ((V m) x) ≤ A!*size (amplify d C Λ x) ∧ size (amplify d C Λ x)≤ A!*size ((V m) x):=by
     let R₁:=C.path.rep N p (m+1); let R:=C.path.rep N p m; have hp:=hw.toll p m N hb ht; obtain ⟨s,K,c,β,T,Q,H,Hs⟩:=hp.author; obtain ⟨hT,hX,hu,hW,hxz,hf,hδ,hV,hζ⟩:=Hs
     obtain ⟨W,z,hG⟩:=Onward.can H (keys0 h ht) h ht hT (hP.legal (m+1) (hb.trans m.le_succ) ht) (Copper.lit _).le hδ hf hV hp.pos.2 hζ
     let e:= keys0 (p:=p) h ht; have he:V m=z:=by
          ext1 x; obtain ⟨x₀,hx⟩:= (hP.legal m hb ht.le).capacity0 (V m x); obtain ⟨y,h_y⟩:= hG.back.capacity0 (z x); apply germ_eyelet hw hx h_y hb ht
          funext q; rw [travels h hP ht hb _ x]; exact (proceeds C p m N d _ _ q (hG.aligned x)).symm
     let r:=trim Λ+ oldCost d K*Doors.rate Λ; let b₀:= Address.margin d c K; have hΩ₁:=H.posp; have hv:=zero_le_one.trans H.cursor.fits; have hΩ : 0≤ b₀:=mul_nonneg (add_nonneg (sCpos hv) (aCpos hv)) (zero_le_one.trans hΩ₁); have hΩ₀: 0≤ beamCost d c K:=by change 0≤ b₀+1+c; linarith; 
     have hxz: 2*Q + beamCost d c K+(1+oldCost d K)≤w₀:= hxz
     have hv':0≤oldCost d K:=by unfold oldCost; positivity
     have hc : c ≤ Q:=by
         apply le_trans _ hδ; unfold clipPrice; let n':=Fintype.card (Mark C d); let t:= beamCost d c K; have h:ahead K c d=2*b₀+1:=rfl; have ht: c≤ c*(1+n'*t):=le_mul_of_one_le_right (zero_le_one.trans hΩ₁) (le_add_of_nonneg_right (mul_nonneg (by positivity) hΩ₀))
         haveI : Nonempty (Mark C d):= by obtain ⟨i⟩:=exists_letter; exact ⟨⟨⟨⟨0,Nat.zero_lt_succ _⟩,i⟩,0⟩⟩
         have he:n' ≥ 1:= Fintype.card_pos
         have hz:= ht.trans (show _ ≤ (c*(1+n'* t))^(d+1) by simpa only [pow_one] using pow_le_pow_right₀ (hΩ₁.trans ht) (show 1≤d+1 from Nat.le_add_left ..)); exact hz.trans (le_mul_of_one_le_left (zero_le_one.trans (hΩ₁.trans hz)) (by exact_mod_cast he))
     have haK: A ≥ (2*b₀+1)*(2*Q):=hζ; have hφ:B d m ≥ 1:=hp.pos.2; have hx:Q≥1:=hΩ₁.trans hc; have ht₀ :1 ≤ A! := by unfold powerFare; rw [max_eq_right hφ];linarith only [hφ]
     have hB : beamCost d c K ≤2* A :=by change b₀+1+c≤2*A; nlinarith only [haK,hφ,hc,hΩ,hx]
     have hc':r ≤ tolerance C m:=by unfold r tolerance; exact add_le_add_right (mul_le_mul_of_nonneg_right (by linarith only [hΩ₀,hf,hxz]) (Doors.rate_pos _|>.le)) _
     have hγ:0 ≤ r:= add_nonneg (Copper.lit _|>.le) (mul_nonneg hv' (Doors.rate_pos _|>.le)); have hX : r≤1:=by have hV:Q*r≤1/2:=hV; nlinarith only [hV,hx,hγ]
     rw [he]; refine ⟨⟨_,_,r,hγ,hc',hG.shape⟩,fun x=>⟨(hG.pays x).2.trans ?_, (hG.pays x).1.trans ?_⟩⟩
     · exact mul_le_mul_of_nonneg_right (show beamCost d c K+r≤A! from by unfold powerFare; rw [max_eq_right hφ]; linarith only [hB,hX,hφ]) (size_ge _)
     apply mul_le_mul_of_nonneg_right _ (size_ge _); unfold powerFare; rw [max_eq_right hφ]; exact (le_mul_of_one_le_left (mul_nonneg zero_le_two hf) (le_add_of_nonneg_left (show 0≤2*b₀ from by positivity))).trans (haK.trans (by linarith only [hφ]))
end YM.RG05Readout.Planes
