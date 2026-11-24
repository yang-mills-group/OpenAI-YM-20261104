import YM.LocalTaylorR2.Marker.Buds
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Marker
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Push.AbsoluteSums Gas Ursell Trees Multiple OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection UVNext Next.Scheduling Ovens Quotes
open Extra.Iteration RG.Shoot Push.SectorMeasure Supply Input Testing Push.PriceCompiler Org UVExtension
open ConnectedActivityE6 PhysicalNext PhysicalNext.Repeat Song Spire Orchard Mast Oasis PhysicalNext.Repeat.Legato
open Tail
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open Progress.DirectedRecipe Roost Opera
open Mallow Blush Lattice Daisy Lotus Daisy.Charity.RG12 UVNext.CouplingReset Extra.Histories Next.Foundations Planned.GuardedAtom
variable {G:Gauge}
variable {M: Metals G} {D:Rolls M.p} {A : Alloy M D} {m j N n d:ℕ} (R:Factor A) (hp:Mallow.RG12.Earned (boltD G) R.shape A.delay) {l v:ℝ}
    (hG:G.Simple) (hm:m<N) {Q: In A.B.a m n} (H:Spring R N m n l v Q)(x:Set.Icc l v)
    (t:Cloud (Q x))(s:Site (A.B.a.S.side m n))(ν:ℂ) {u₀:ℕ→ℝ}{V:Bid.Worth}(Y:PhysicalNext.Repeat.Legato.Bandage R u₀ V)
local notation "P" => A.B.a.clock
local notation "T" => A.B.a.params m
local notation "b" => A.B.a.budget m
local notation "w"=>authors A.B.a m
local notation "χ" => A.B.a.clock.hatBeta m
local notation "x'"=> A.B.a.clock.hatBeta (m+1)
local notation "ψκ"=> A.B.a.clock.forcedAllowance m
local notation "Jp" => A.B.a.clock.J (m+1)
local notation "Ip" => A.B.a.clock.J m
local notation "s!"=> A.B.a.S.side m n
local notation "W"=> houseS H x
local notation "Θ"=> R.shape.μ Jp Ip
local notation "L₁"=> D.L Jp
local notation "Z'"=> scope W t s
set_option quotPrecheck false
local notation "π'"=> localSection G d
local notation "F'"=> (Labels.frames G).level d
local notation "R2" => H.result x
local notation "Pp" => (R.target Jp Ip)
local notation "Oo"=> (A.B.a.clock.op m n)
local notation "p0"=> pupil H x t.live
local notation "p1"=> pupil H x t.pale
local notation "Vc"=> plaque (p0) (p1) ν

variable (hd:d ≤ A.B.a.clock.J m) (h:s∈ t.live.crest.image (A.B.a.clock.op m n).ratio.parent) {ε:ℝ}
include hp hd
local notation "FF!" => fee G (D.L Jp) (A.B.a.params m) d
local notation "Mk"=> markBill t.live Pp
local notation "Mk0"=> CalendarStep.loss Jp
local notation "v!"=> colorShot (d:=d) R H x t ν
local notation "sp!"=> spur (d:=d) R H x t ν
local notation "T0"=> Real.sqrt (ψκ)
local notation "f!"=> flash (d:=d) R x t ν
local notation "E!"=> stick (d:=d) R x t ν
local notation "α!"=>R.pledging.conducts.full

omit hp hd
lemma renature (p : ℕ): Segment (v!) ((sp!) p false) ((sp!) p true):=by
  refine ⟨?_,?_,?_⟩
  · change _ = 0+(0:(F').Coeff); rw [zero_add]; rfl
  · let A:=fun (_:(houseS H x).fragrances) (q:ℕ)=> p+1 ≤ q
    have h:= voyage (W) t A ν p
    unfold spur colorShot screen; simp only []; simpa only [flakes,Bool.false_eq_true,ite_false,ite_true] using! h
  unfold colorShot screen spur; simp

lemma monotonicF {E F:ℝ}(hE:E≤ F): (f!) E≤(f!) F:=by unfold flash; have hP:= marknn R x t; have hh:= uncoupled G T d L₁; gcongr
lemma agency (ε:ℝ)(he:0 ≤ ε): 0 ≤ (f!) ε ∧ (f!) ε ≤ E!*ε ∧ Local.factor (hol G) (π') (R2).p.supportExponent w*(f!) ε ≤ E!*ε:= by
   obtain ⟨h1,h2,h3⟩:= light G L₁ T d ε Mk ν he (marknn R x t); exact ⟨h1,h2,h3⟩
-- H.mk portrait numbers at Fine.PROFIT.With true HP.
include hG hm h Y hp hd
lemma coal (p:ℕ)(hy:p ≤ Jp) : Push.Local.ForceCost (R2).p (R2).activities Vc (T0*(f!) (x'^(-(p+1:ℝ)))):=by
   have hu:=(debts R hp hd p hy W); have hx:=(care R hG hm H x t s ν Y h d).2.2
   let U:= FF!; let a:=x'^(-(p+1:ℝ)); let fS:= Mallow.straw Θ L₁ G χ -- shadow W notation illegal
   have he := forceUsage hu
   rw [← PriceCompiler.beta_eq A.B.valid] at he
   let g:=(Pp).goal L₁ χ; let y:=glyph χ; have hh:0<y:= Blush.glyphpos χ; have hk:= uncoupled G T d L₁
   have h' : g⁻¹*(y⁻¹*fS) ≤ a/U:= (le_div_iff₀ hk).mpr (mul_comm ..|>.trans_le he)
   apply larger hx
   rw [Blush.glyph_eq]
   change 2*‖ν‖*(Mk /g *fS)≤ y*(2*‖ν‖*(Mk*(a/U)))
   calc
     _ = y*(2*‖ν‖*(Mk*(g⁻¹*(y⁻¹*fS)))):= by rw [div_eq_mul_inv]; field_simp -- ginv maybe fails
     _ ≤ _:= by have h₀:= marknn R x t; gcongr

local notation "Ci" u:arg=> CanvasOut u (hol G) (π') s (Z') (R2) (T0) (ψκ) w
lemma shaping (p:ℕ)(hi:p ≤ Jp)(c:ℝ)(hc: x'^requested (p+1) Mk0 ≤ c):
   let e:= f! (x'^requested 0 Mk0); let f:=f! c; let g:=f! (x'^(-(p+1:ℝ))); let y:= E!*c; let u:=E!*x'^requested 0 Mk0
   (v!).eval s Z' (localSection G d) R2=ν • ((Oo).push (Q x|>.beta) t.milk) ∧
   Segment v! ((sp!) p false) ((sp!) p true) ∧ (Ci (v!)) (e+f) g (u+y) ∧
   (Ci ((sp!) p false)) e 0 u ∧ (Ci ((sp!) p true)) f g y ∧
   (v!).eval s Z' (π') R2=((sp!) p false).eval s Z' (π') R2+((sp!) p true).eval s Z' (π') R2:= by
   intro e f g y u
   have hY:= H.moves hG hm |>.2 x x.property|>.1.bundle.valid
   obtain ⟨hA,hV,hP⟩:= care R hG hm H x t s ν Y h d
   have hx:= coal R hp hG hm H x t s ν Y hd h p hi
   let U:= (sp!) p false; let U':= (sp!) p true
   have hS:=renature (d:=d) R H x t ν p
   have hα : Modesty G (R2).p s (Z') U.bulk e:= earnsAny R hp hm H x t s ν hd h _ 0 (fun _ i=> flakes p false i) hi (Nat.zero_le _) (fun _ i _=> Nat.zero_le i)
   have hU := hA.force; let B:= (R2).p
   have ht : 0 ≤ x':=zero_le_one.trans (A.B.a.fits.delayed _).le
   have hX':0≤ x'^requested 0 Mk0:= Real.rpow_nonneg ht _
   have hK:0≤ c:= (Real.rpow_nonneg ht _).trans hc
   have hu := agency R H x t ν (d:=d) _ hX'
   have hh := agency R H x t ν (d:=d) _ hK
   have hT : U'.forced=Vc:=by unfold U' spur; simp
   have hT' : U.forced=0:=by unfold U spur; simp
   have hf (u':ℕ): flakes p true u'→ p+1≤ u':=by simp [flakes]
   have hβ : Modesty G (R2).p s (Z') U'.bulk f:= Modesty.rise (earnsAny R hp hm H x t s ν hd h p _ (fun _ i=> flakes p true i) hi le_rfl (fun _=>hf)) (monotonicF (d:=d) R x t ν hc)
   have hm': (Ci U) e 0 u:=⟨⟨hA.origin,hα.regular,by rw [hT']; exact vacant⟩,hα,by rw [hT',mul_zero]; exact costless le_rfl,rfl,hu.2.2⟩
   have hm'': (Ci U') f g y:= ⟨⟨hA.origin,hβ.regular,by rw [hT]; exact hU⟩,hβ,by rw [hT]; exact hx, rfl,hh.2.2⟩
   exact ⟨hV,hS,⟨hA,hα.add hS hβ,hx,rfl,(by rw [mul_add]; exact add_le_add hu.2.2 hh.2.2)⟩,hm',hm'',pieces hS (π') hY.labels.boundK hα hβ hm'.packets hm''.packets⟩ -- hα.add arg

open Guard
variable (D':Guard.Berths (H.result x).p (H.result x).activities (fun i=>Push.Local.joint (localSection G d) s (Blush.scope (houseS H x) t s i)))

structure Engine (p:ℕ) (c:ℝ) (D₀:Guard.Berths (H.result x).p (H.result x).activities (fun i=>Push.Local.joint (localSection G d) s (Blush.scope (houseS H x) t s i))): Prop where
   mileage : let U:= (sp!) p false; let U':= (sp!) p true
             let e:= (f!) (x'^requested 0 Mk0); let f:= (f!) c; let g:= (f!) (x'^(-(p+1:ℝ))); let y:= E!*c; let u:=E!*x'^requested 0 Mk0
             -- give all scopes, including sensor `x` errors after actual projection, no fake Frame equivalence
             let Φ (i : Local.Raw F' s!):= Guard.mint D₀ i (hol G)
             let priced (i:Local.Raw F' s!)(a c:ℝ) (d1:ℝ):= (Ci i) a c d1 ∧ -- fix type & capture d
                (Φ i).Format s (hol G) (R2) ∧ (Φ i).support=(fun i=> Local.joint (π') s ((Z') i)) ∧ (Φ i).density s (π') (R2) = i.eval s Z' (π') R2 ∧ Planned.GuardedAtom.Tab (Φ i) s (R2) T0 d1 (c+d1) ∧ (F').coeffSize (Φ i).x ≤ d1
             priced (v!) (e+f) g (u+y) ∧ priced U e 0 u ∧ priced U' f g y ∧ (Φ (v!)).density s (π') (R2)=ν • ((Oo).push (Q x|>.beta) t.milk) ∧
             Segment (v!) U U' ∧ Hinge (Φ (v!)) (Φ U) (Φ U') ∧ (Φ (v!)).density s (π') (R2)=(Φ U).density s (π') (R2)+(Φ U').density s (π') (R2) ∧
             ( e≤u ∧ f≤y ∧ g ≤ E!*x'^(-(p+1:ℝ)))

lemma ships (p:ℕ)(hc:x'^requested (p+1) Mk0≤ ε) (hi:p ≤ Jp): Engine R H x t s ν p ε D':=by
   obtain ⟨hθ,hδ,hX,h1,h2,h3⟩:=shaping R hp hG hm H x t s ν Y hd h p hi ε hc
   have hY:= H.moves hG hm |>.2 x x.property|>.1.bundle.valid
   have hr: Local.Readable (hol G) (π') (R2).p s! w:= Graces.lively Y.clock hd
   have hx: 0< ψκ:= Extra.Histories.forcedPos ..; have hb:=Real.sqrt_pos.mpr hx
   have hB: Local.hitWidth (R2).p*T0≤1:= by rw [Blush.glyph_eq]; exact (Y.stamp _ _ (step_paid A.B.a m) _ hd χ (A.B.valid.pays m)).2 A.B.a m (params_eq A.B.valid m) rfl
   have ht:=CanvasOut.booked _ D' hr hY hX hx hB; have ha:=CanvasOut.booked _ D' hr hY h1 hx hB; have hw:=CanvasOut.booked _ D' hr hY h2 hx hB
   constructor; intro U U' e f g y u Ψ pf
   have hB':(∀ v:ℝ, 0≤ x'^v):= fun _=> Real.rpow_nonneg (zero_le_one.trans (A.B.a.fits.delayed _).le) _
   exact ⟨⟨hX,ht⟩,⟨h1,ha⟩,⟨h2,hw⟩,ht.2.2.1.trans hθ,hδ,
     hinge D' hr hδ h1.format h2.format (CanvasOut.rows _ hr h1 hx hB) (CanvasOut.rows _ hr h2 hx hB),
     (ht.2.2.1.trans h3).trans (congr_arg₂ (·+·) ha.2.2.1.symm hw.2.2.1.symm),
     (agency (d:=d) R H x t ν _ (hB' _)).2.1,(agency (d:=d) R H x t ν _ ((hB' _).trans hc)).2.1,(agency (d:=d) R H x t ν _ (hB' _)).2.1⟩
end YM.LocalTaylorR2.Marker
