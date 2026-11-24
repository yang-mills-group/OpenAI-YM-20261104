import YM.LocalTaylorR2.Grafting.Road
import YM.LocalTaylorR2.Grafting.Seal
/-! Adapt Sustained  On the genuine Canopy desks. Demands explicit same-time pickups. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Mallow.Many
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity Rain Roost Lotus
open UVNext.CouplingReset Animals Marlin Progress.DirectedRecipe Ovens Ovens.Pipes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} (g:G.Simple) {X:Metals G} {D: Rolls X.p} {A : Alloy X D}
    {R: Factor A} {l v:ℝ} {N m n:ℕ}(hm:m<N) {Q: In A.B.a m n} (H: Spring R N m n l v Q)
local notation "I" => Icc l v
local notation "L" => D.L (A.B.a.clock.J (m+1))
local notation "Θ" => A.B.a.S
local notation "J" => A.B.a.clock.J (m+1)
local notation "Jp" => A.B.a.clock.J m
local notation "K" => A.B.a.params m
local notation "wT" => radiusB (A.B.a.clock.hatBeta m)
local notation "gV" => A.B.kin.alpha N m
local notation "B" => A.B.a.budget m
local notation "d" => H.ordinal
local notation "Y" => R.target J Jp
local notation "Ze" => R.expense J Jp
local notation "Cμ" => (R.shape.μ J Jp)
local notation "y" => A.B.a.clock.hatBeta m
local notation "O" => Chi.canonical
local notation "X₀" => H.H.base
variable (x: Icc l v)
local notation "W" => houseS H x
local notation "f'" => H.H.sister x
local notation "Tap0" => graft H.H H.knows H.W d x.val
open YM.Merge
open MergeProof Menu
variable (hE : (Q x).p.supportExponent≥100)(hN : 100≤(H.result x).p.supportExponent) (hS: Arrives R.shape A.delay) (hF:Pungent R.shape A.delay)
open YM.LocalTaylorR2 Orbit _root_.YM.Marker MergeProof.Accent
variable (hP : Mallow.RG12.Earned (Mallow.orbitD G) R.shape A.delay) (lP:ℕ)
variable {ι P:Type} [DecidableEq P] [Fintype P][Fintype ι]
  (C:_root_.YM.Marker.Census P)(b₀:ι→Menu.Hat C (Q x))(o:P→ Site (A.B.a.S.side (m+1) n))(r:P→ℝ)
set_option quotPrecheck false
local notation "o₀"=> (A.B.a.clock.op m n).ratio.parent ∘ o
local notation "F"=> H.result x
local notation "B'"=> (B).supportExponent
local notation "b₁"=> F -- unused
local notation "s₀"=> Mallow.straw Cμ L G y
local notation "P'"=> (A.B.a.budget m)
local notation "F'"=> A.B.a.clock.op m n
local notation "tx"=> (A.B.a.clock.hatBeta (m+1))
local notation "u₀"=> Mallow.station tx
local notation "u'"=> CalendarStep.loss J
local notation "Θ'"=> (houseS H x)
local notation "M'"=> fun i=> (b₀ i).M
local notation "M₀"=> fun i=> Menu.sumFee (b₀ i) r
local notation "M₁"=> fun i=> Menu.sing (b₀ i) r
local notation "g'"=>pupilK H x M' M₀
local notation "d0"=> Mallow.sandboxK H x
open Tail
open Reel (Strand)
variable (ψ: Reel.Scroll G (A.B.a.S.side (m+1) n)) {v₁ p₀ pz:ℝ}
variable (hv:Reel.Affords (Q x) A.B.a (m+1) ψ v₁) (hR:Mallow.RG12.Earned (Mallow.roadD G) R.shape A.delay)
local notation "γ"=> A.B.a.clock.allowance (m+1)
local notation "Θ!"=> Reel.Strand.spelling lP
local notation "δ!"=> (2*v₁/(γ))
local notation "ϕ"=> (tx ^ (3:ℕ)) -- NOTE `χ^3.1?` compute
local notation "θ"=> (tx^(21/10:ℝ))
local notation "scout!"=> Orbit.shop W C r o₀ (B)
local notation "Pt"=> (H.result x)
local notation "H!"=> (tx ^ Tail.requested (lP+1) (u'))
abbrev preview (F₀:∀ i:(W).fragrances,Finset (Booking (W) M' lP i)):= fun i=>measureS (W) O M' M₀ C M₁ lP i (F₀ i)
-- vekker ephemeral; NOT related to varying χ/per-hour
structure Assisted (φ Δ b :ℝ) : Prop where
   strong: StrongR2 H x lP C b₀ o r φ
   parts : Adjusted W O M' M₀ C M₁ lP r o₀ Pt g' ψ (u') (Δ+φ) φ -- typo
   early (F₀:∀ i:(W).fragrances,Finset (Booking (W) M' lP i)) (i:ℕ) (hp:i ≤ lP+1)
      (hF:∀ k j,j∈ F₀ k→ i ≤ ranked (W) M' lP k j ∧ ranked (W) M' lP k j ≤ lP):
        scout! (chef W O M' M₀ C M₁ lP F₀ ψ) (tx^requested i (u')) ∧ scout! (preview H x lP C b₀ r F₀ - chef W O M' M₀ C M₁ lP F₀ ψ) (b*tx^requested i (u'))

include hR
lemma numericWidth (hl:lP ≤ J)(b:ℝ)(hb:0≤b): Θ! * (2*b/(γ)) ≤2*θ * b ∧ 2*θ * b * tx^requested 0 (u') ≤ (2*ϕ)*b:=by
   have ht : 1≤ tx:=(A.B.a.fits.delayed _).le; let z:=tx
   have hz :0<z:= zero_lt_one.trans_le ht; let a:=CalendarStep.loss J; have he:a≤1:= inv_le_one_of_one_le₀ (by linarith [show 0 ≤ (J:ℝ) from Nat.cast_nonneg _]) -- check
   have hv: Θ! ≤ tx:= by rw [beta_eq A.B.valid]; exact (hR _ _ (A.B.valid.pays m) _ (step_paid A.B.a m)).1 lP hl
   rw [show γ=δE tx from rfl, Reel.dto hz, Real.rpow_neg hz.le]; simp only [div_inv_eq_mul]
   constructor
   · apply le_trans (mul_le_mul_of_nonneg_right hv (show 0 ≤ 2*b*z^(11/10:ℝ) by positivity))
     rw [show (21/10:ℝ)=1+11/10 from (by norm_num),Real.rpow_add hz,Real.rpow_one]; apply le_of_eq; ring
   let y':=requested 0 a
   calc _ = 2*b*z^((21/10:ℝ)+y'):= by rw [Real.rpow_add hz (21/10:ℝ) y']; unfold y' a z; ring
        _ ≤ 2*b*z^(3:ℝ):= mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le ht (by unfold y' requested; push_cast; linarith only [he])) (by positivity)
        _ = _:= by rw [show (3:ℝ)= ((3:ℕ):ℝ) from rfl, Real.rpow_natCast]; unfold z; ring
open Capstone
include hm hv
-- NOTE existing budgeted contains real transforms. output funded without arbitrary θ repr.E'
set_option maxHeartbeats 700000 in
lemma coherent (hstrong: StrongR2 H x lP C b₀ o r p₀) (hb:∀ i,0<r i) (ht: Menu.Offer o b₀ r (Q x).p.B ((Q x).p.supportExponent-4) u₀) (hl:lP ≤ J)
    (hΩ:2*ϕ*v₁ ≤ pz): Assisted H x lP C b₀ o r ψ p₀ pz (2*θ*v₁):= by
   let Z:= houseS H x; let t:=(v₁); let Fε := (u'); let Gx:= numericWidth (m:=m) (R:=R) lP hR hl t hv.leftB.le -- arguments check
   have hR':=hR _ _ (A.B.valid.pays m) _ (step_paid A.B.a m); have hs:= Z.laws.data.funds
   have ha:= hR'.2 ⟨(F').patch,hs.funds.kernel,hs.length_eq,hs.funds.atStep⟩ lP hl
   have hF:(B).order=(X.p.profile Jp).order:= congr_arg RG.Stage.order (params_eq A.B.valid m); have hn:(B).power=(X.p.profile Jp).power:= congr_arg RG.Stage.power (params_eq A.B.valid m); rw [← hF, ← hn] at ha
   have hx : tx=betaF G y L:= beta_eq A.B.valid m
   have hy : (B).supportExponent+3 ≤ (Ze).earn:= by
        have he':= R.pledging.agenda _ _ (step_paid A.B.a m)|>.1; rw [Rain.jersey (A:=A) (m:=m)|>.2.2.1]; linarith
   have hr(i): (b₀ i).s.val.image ((F').ratio.parent ∘ o) ⊆ (M' i).crest.image (F').ratio.parent:=by intro j hj; obtain ⟨i',hi,hj⟩:= mem_image.mp hj; subst j; exact mem_image_of_mem _ (ht.sites _ (mem_image_of_mem _ hi))
   have hX'(i): GridApprox.Nil.Scoped {xΩ| o₀ xΩ∈ (M' i).crest.image (F').ratio.parent} (M₁ i):= GridApprox.Nil.scope_send _ _ _ ((Accent.room _ _ _).2 (hr i))
   have hY:= hstrong.plot
   obtain ⟨hp,hf⟩:= H.knows x x.2
   let φ:= (γ/(2*v₁)) • (ψ-(Q x).activities.E); let gq(i:Strand):=(Q x).activities.E+Reel.Strand.dial i • φ
   have hk(i:Strand): PartialLives A.B.bake N (m+1) n (Reel.bend (Q x) (gq i)):= ⟨hp.path,hp.point,hp.clip,hv.stamps i⟩
   choose A₀ hA using fun i=> Opera.partial_feature A.B R.shape hm R.pledging.conducts.full R.pledging.conducts.income (hk i) (show (Reel.bend (Q x) (gq i)).beta ∈ _ from hf)
   obtain ⟨g,hg,hL,hL'⟩:= Reel.blend_it hv; change gq g=ψ at hL'
   let Bk:= B; let v:= ℝ -- remove
   have hS:= Opera.protocol A.B hm R.pledging.conducts.full (n:=n)
   have hN(i): Marker.Poly.price r (M₁ i) ≤1:= Menu.paid (b₀ i) hb
   have hU (f:∀ i:(W).fragrances, Finset (Booking W M' lP i)) (i:ℕ)(hp:i ≤ lP +1)(hF:∀ k j,j∈ f k → i ≤ ranked W M' lP k j ∧ ranked W M' lP k j ≤ lP):
        scout! (chef W O M' M₀ C M₁ lP f ψ) (tx^requested i (u')) ∧ scout! (preview H x lP C b₀ r f - chef W O M' M₀ C M₁ lP f ψ) (2* θ * v₁ *tx^requested i (u')):=by
     have hp' k j hh := hF k j hh|>.1
     have ht :0≤ (tx^requested i (u')):=Real.rpow_nonneg (zero_le_one.trans (A.B.a.fits.delayed _).le) _
     have hv' := Orbit.steadyG W O M' M₀ hY C M₁ lP (fun k j hk=>(hF k j hk).2) φ A₀ r hb hN o₀ hX' g hg (B) rfl rfl (Ze) hy hS ha i hp hp'
     have hA':= shopScale _ _ _ _ hv' (-1); rw [norm_neg,norm_one,one_mul,neg_one_smul, neg_sub] at hA'
     rw [← hL']; refine ⟨hx.symm ▸ (Orbit.blueParts W O M' M₀ hY C M₁ lP r hb hN o₀ hX' (B) rfl rfl f (gq g) (J':=A₀ g) (Ze) hy ha hS hp hp'),opened W C r o₀ hA' ?_⟩ -- hx.symm ▸ wrongly replaces W deps!
     rw [← hx,hL]; exact mul_le_mul_of_nonneg_right Gx.1 ht
   let Fc:= fun i=> apportion W M' lP i (fun t=> if true=true then ¬ lP+1 ≤t else lP+1 ≤t)
   obtain ⟨hS',hb'⟩:= hU Fc 0 (Nat.zero_le _) (fun i j he=> ⟨Nat.zero_le _,by unfold Fc apportion at he; simpa [Nat.lt_add_one_iff] using he⟩)
   rw [hx] at hS'; exact ⟨hstrong,payBack W O M' M₀ C M₁ lP r hb o₀ Pt g' ψ hstrong.carry hS' (opened W C r o₀ hb' (Gx.2.trans hΩ)),hU⟩
end YM.PhysicalNext.Repeat.Mallow.Many
