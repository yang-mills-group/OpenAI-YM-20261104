import YM.MSbar.Mosaic.Bee
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.MSbar.Mosaic
open Function Filter MeasureTheory Precision Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Gauge Midpoint Rolling Exterior Wilson Wave Lis Cypress Topology
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Bakery.Portal Further.GaussianScalar Jade Kelvin Bout Parma Tramp Heath Stock Heath.Cottage Film
open Measuring Cane Laurent Bloch UVNext.PricedKernels Spruce Lapaz Ruby
open Next.SectorChange Bulk Posture JetTab
variable {G:Gauge}
namespace Issue
variable {ι:Type}{X f' g H0:ι→ℝ}{A:ι→Issue G}{φ:Filter ι}[φ.NeBot] (hX:Tendsto X φ atTop) (χ:ChartRatio G)(J:Voice G)(H H':Stage)(K:Patch)(D:KernelChoices)
variable (hG:G.Simple) (hD:K.Branches D G)(hQ: Clear G J)(hχ:LocalRatio χ)
local notation "α'" i=> tip G K.L (X i)
local notation "Y"=> fun i:ι=> tip G K.L (X i)
local notation "w'" i=> vol (tip G K.L (X i))
local notation "t'" i=> (A i).fClock
variable (hp:∀ᶠ i in φ,Paid (A i) K H H' J (X i)) (hq:∀ᶠ i in φ,(A i).S.kernel=D)
variable (W:(i:ι)→Positions (Primary (A i).c G))(hW:∀ᶠ i in φ,‖W i‖ ≤ hull (X i))
variable {p m k q L:ℕ}
variable (M:StageCost)(i':G.ColorIndex){s' e ν b:ℝ}(hc:∀ᶠ i in φ,Festival (A i) χ p i' ∧ ClockD (A i) p m M.s (X i)∧ Cs (A i) χ M.s p m (X i) i' (f' i) b ∧ Issue.Receipt (A i) M (X i))
variable (z:(i:ι)→Site (A i).f)
local notation "λ'" i=> Cane.value (αm i) M.C M.A M.E M.s M.sway
variable (hR:∀ᶠ i in φ,Ore M (X i) K) -- conduit.
variable (P:Palisade){τ b' :ℝ}(B :ℝ)
local notation "x'" i=> boxX (tip G K.L (X i)) (z i)
local notation "x₁" i=> boxY (tip G K.L (X i)) (z i)
noncomputable def gear(m:ℕ)(c T V X r ξ ρ:ℝ) : Salary := ⟨c,T,V,m,X,T*(1+r)^m,V*(1+r)^m,1,ξ,ρ,0⟩
local notation "N"=> k*(p+2)
local notation "N'" i=> Fintype.card (Lake (A i).F (boxX (α' i) (z i)) G)
local notation "N₁" i=> (keepB (A i).F (x' i) G).card
local notation "N₂" i=> (keepF (A i).F (x' i)).card
local notation "Γ" i=> crownP (A i).F (A i).M (W i)
local notation "Φ'" i=> inkW (N₂ i)
variable (h₁:p+2 ≤ m)(ha:Run φ X f' 0)(hk:k=m+1)(hT:p+3≤ k)(hμ:4 ≤ m)(hb:0<τ)(hb':0≤b')
variable (hK:∀ᶠ i in φ, Issue.Buy (A i) (W i) (boxX (tip G K.L (X i)) (z i)) (boxY (tip G K.L (X i)) (z i)) J P χ (tip G K.L (X i)) e s' (thorn (tip G K.L (X i)) (k*(p+2))) τ b')
include hX hp hc hR hW hχ hG hQ h₁ ha hk hT hμ hb hb' hq hK
-- choose all arrays independent of U inside. true film.Tribe bound.Emark.P.States. includes luminosity `E` meas.
structure Projection (A:Issue G)(χ:ChartRatio G)(P:Palisade)(J:Voice G)(O:Ages) (W:Salary)(Z:Positions (Primary A.c G))(p k:ℕ)(U₀:Site A.f)(x:ℝ)(T K' E E' D:ℝ):Prop where
     digs : 1 ≤ O.outer
     vlog : O.w = vol x
     throne : ‖Rolling.throne A.F A.ρ Z‖≤ O.outer
     epic : O.Vying p k A.fClock A.T A.F A.pre χ A.v
     funds : Issue.Port A J χ P O W x k Z p (k*(p+2)) (crownP A.F A.M Z) (boxX x U₀) (boxY x U₀) T (Bmark G (k*(p+2)) 0 p k (A.S.patch.L.val* closeN x) U₀ K' O.outer (αm x)) (αm x) E D
     payQ (n:ℕ)(he:n≤ k) : let s:= A.S.patch.L.val*closeN x;
       Emark O (Bmark G (k*(p+2)) 0 p k s U₀ K' O.outer (αm x)) (barry 0 (k*(p+2)) p ((liftW (αm x) 0 s)* K') O.outer) A.fClock k n p ≤ E'
variable (hB: 0≤ B)(hT₁: Run φ (fun i=> tip G K.L (X i)) H0 0)(he1:∀ᶠ i in φ,0 ≤ H0 i)
include hB hT₁ he1
local notation "V'" i=> ((A i).S.patch.L.val*closeN (Y i))
local notation "Y'"=> Y
-- split. Runtime.
structure Temper (A:Issue G)(J :Voice G)(P:Palisade)(χ:ChartRatio G)(Q:Ages)(p k:ℕ)(x v:ℝ)(Z:Positions (Primary A.c G))(Y_:Site A.f):Prop where
     check_ : Q.Vying p k A.fClock A.T A.F A.pre χ A.v
     origin : Q.w= vol v
     dollars : 1 ≤ Q.outer
     upper : ‖Rolling.throne A.F A.ρ Z‖ ≤ Q.outer
     fees : ∀ i:Body 1 A.f,‖ran (crownP A.F A.M Z) i‖ ≤ Q.r
     march : ∀ (U':Config G A.f),U'∈ hotel A.F (boxX v Y_) (boxY v Y_) J (postcard G A.c A.fClock Z) (venueX A Z) (pillow v) (room v) → ∀ i:SpaceP A.F (boxX v Y_) G,
            i∈ clipM A.F (boxX v Y_) (boxY v Y_) (hotel A.F (boxX v Y_) (boxY v Y_) J (postcard G A.c A.fClock Z) (venueX A Z) (pillow v) (room v)) χ A.fClock (sampleY A.F A.pre A.v J (boxX v Y_) (boxY v Y_) U' (A.fClock • Z) ∘ includeX A.F (boxX v Y_)) U' →
            let K:= berth A.F A.pre A.v J (boxX v Y_) (boxY v Y_) U' Z A.fClock i
            let p:= stamp A.F G K
            let s:= Tilt.regal (crownP A.F A.M Z) p 1
            ‖meetVar Z K‖≤ Q.outer ∧‖tint G _ p‖≤ Q.r ∧ ‖s‖+Q.b*A.fClock*Q.r^2 ≤ Q.w ∧ ‖s‖ < Q.w/2
omit hB hT₁ he1
lemma stockS : ∃ (c1 c2 c3 c4 k1 k2 tx :ℝ) (U V ψ:ι→ℝ), Run φ Y ψ 0 ∧ Run φ Y U 0∧ Run φ Y V 0 ∧0≤k1∧ ∀ᶠ i in φ,
      let Q:= Ages' c1 c2 c3 c4 (U i) (V i) tx (ψ i) k1 k2 (5*goalP (Y i) p) (vol (Y i)); Temper (A i) J P χ Q p k (X i) (Y i) (W i) (z i):=by
    obtain ⟨U,V,hU,hV,Hx,Hk⟩:= Issue.sizes hX χ J H H' K hG hp W hW M i' hc hR P
    obtain ⟨a,b,c,d,k1,k2,tx,ψ,hΨ,hy⟩:= Issue.award hX χ J H H' K D hG hQ hχ hp hq M i' hc h₁ ha hk hT hμ U V hU hV (Hx.mono (fun i hx=>⟨hx.1,hx.2.1⟩))
    obtain ⟨_,hh⟩:= hy.exists
    refine ⟨a,b,c,d,k1,k2,tx,U,V,ψ,hΨ,hU,hV, (show Jade.Vows .. from hh).posC,?_⟩ -- syntactic cast
    have ht':= shapeK hX J H H' K hG hp W hW
    filter_upwards [hp,hK,hc,hW,Hx,Hk b, hy, ht'] with i hp hK ⟨h,he,hz,hf⟩ hw hh hB hy ht O
    let Nq:=A i
    obtain ⟨h₀,h₁,h₂,hv,H_size,H_r,H_l,H_b⟩:=hh; let v0:=Alto.cWidth (X i)/(Nq.S.patch.L.val:ℝ); let Q:= hK.price; have h₀':0 ≤ v0:=div_nonneg (div_nonneg zero_le_one (sq_nonneg _)) (Nat.cast_nonneg _)
    obtain ⟨X',hF⟩:=h.preT; have hp':0 < t' i:=ht.2.1; let D':=hf.seats
    refine ⟨hy,rfl,h₁,?_ ,?_, ?_⟩
    · have he:= Ruby.lotus (A i).F (A i).pre (A i).v (W i) (A i).ρ (A i).M h₀' hf.seats; change ‖meetVar (W i) (center (A i).F (A i).ρ (W i))‖ ≤ _; rw [norm_meet]; exact max_le (hw.trans h₂) (he.trans ((mul_le_mul_of_nonneg_left hw (zero_le_one.trans D'.land.cash)).trans hv))
    · exact fun j=> (Ruby.tends (A i).F (A i).pre (A i).v (W i) (A i).ρ (A i).M h₀' hf.seats hw j).trans H_l
    have hpv:0 ≤ vol (tip G K.L (X i)):=div_nonneg (sq_nonneg _) (by norm_num)
    intro u hu; refine Ruby.carve (A i).F (A i).pre (A i).v J χ (x' i) (x₁ i) u (t' i) (W i) (A i).ρ (hK.spot) hp' hu (A i).M O h.critical h.guessed hF.quiet hQ hp.payments.bends.1 hK.price.first.extendsX hf.slope h₀' hf.seats hw h₂ H_size H_r H_l ?_ ?_|>.2 -- X₀ notation name lowercase etc order
    · have hx: O.b *_*O.r^2 ≤ O.w/4:=hB; apply le_trans (add_le_add H_b.le hx); change vol (α' i)/4+vol (tip G K.L (X i))/4 ≤ vol (tip G K.L (X i)); linarith only [hpv]
    apply lt_of_lt_of_le H_b; change vol (tip G K.L (X i))/4 ≤ vol (tip G K.L (X i))/2; linarith only [hpv]
end Issue
end YM.MSbar.Mosaic
