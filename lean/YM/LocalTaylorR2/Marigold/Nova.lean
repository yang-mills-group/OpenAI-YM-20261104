import YM.LocalTaylorR2.Marigold.Door
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
-- retains TOTAL E + K and assigns only branch perturbation as Main. Compared to original `ψ`, canonical raw difference reads full φ and K evaluations. Doesn't require combining an inauthentic Guard.T.Comparer
variable (ψ: Reel.Scroll G (A.B.a.S.side (m+1) n)) (p:ℕ)(Ξ:King.Engine G)
abbrev nova : Push.Local.Raw F' s!:= ⟨0,highball W t (fun _ i=> flakes p false i) ν ψ Ξ p,0⟩
abbrev ordinate : Push.Local.Raw F' s!:= ⟨0,(v!).bulk-(nova (d:=d) R H x t ν ψ p Ξ).bulk,(v!).forced⟩
local notation "κ!"=> nova (d:=d) R H x t ν ψ p Ξ
local notation "ω!"=> ordinate (d:=d) R H x t ν ψ p Ξ
open RG Local
open Guard
-- inline Pose from `Engine`
variable (D':Guard.Berths (H.result x).p (H.result x).activities (fun i=>Push.Local.joint (localSection G d) s (Blush.scope (houseS H x) t s i)))
structure RatioNova (c a:ℝ):Prop where
   before : Registry R H x t s ν ψ p D' c a
   margin :
             let e:= (f!) (x'^requested 0 (Mk0/2)); let f:= (f!) (c+a+c); let g:= (f!) (x'^(-(p+1:ℝ))); let y:= E! *(c+a+c); let u:=E! *x'^requested 0 (Mk0/2)
             let φ (i : Local.Raw F' s!):= Guard.mint D' i (hol G)
             let priced (i:Local.Raw F' s!)(a c:ℝ) (d1:ℝ):= CanvasOut i (hol G) (π') s (Z') (R2) (T0) (ψκ) w a c d1 ∧
                (φ i).Format s (hol G) (R2) ∧ (φ i).support=(fun i=> Local.joint (π') s ((Z') i)) ∧ (φ i).density s (π') (R2) = i.eval s Z' (π') R2 ∧ Planned.GuardedAtom.Tab (φ i) s (R2) T0 d1 (c+d1) ∧ (F').coeffSize (φ i).x ≤ d1
             priced (κ!) e 0 u ∧ priced (ω!) f g y ∧ (φ (v!)).density s (π') (R2)=ν • ((Oo).push (Q x|>.beta) t.milk) ∧
             Segment (v!) (κ!) (ω!) ∧ Hinge (φ (v!)) (φ (κ!)) (φ (ω!)) ∧
             (φ (v!)).density s (π') (R2)=(φ (κ!)).density s (π') (R2)+(φ (ω!)).density s (π') (R2) ∧ f ≤ y
-- modesty.add variants abstract
local notation "Cp₀" α:arg => CanvasOut α (hol G) (π') s (Z') (R2) (T0) (ψκ) w
variable {ε' uP :ℝ}(hH:Mallow.RG12.Earned (keyD G) R.shape A.delay)(hD:Mallow.RG12.Earned (roadD G) R.shape A.delay)
  (ht: Reel.Affords (Q x) A.B.a (m+1) ψ uP)
include hp hm hG h Y hd hH hD ht
lemma pillars (hq:Mallow.RG12.Earned (roomD G Ξ) R.shape A.delay)(hv:2*x'^ (3:ℕ)*uP≤ ε')(hy:x'^requested (p+1) Mk0≤ ε)(hi:p ≤ Jp): RatioNova R H x t s ν ψ p Ξ D' ε ε':=by
   let K':=(κ!); let B':=(ω!); let S:= (v!); let y:=x'^requested 0 (Mk0/2)
   have h₁ := shaping R hp hG hm H x t s ν Y hd h p hi ε hy
   obtain ⟨hθ,hδ,hX,h1,h2,h3⟩:=h₁
   let F := (fun (_:(W).fragrances) i=>flakes p false i)
   obtain ⟨hy1,hz⟩:= highwaysG (f':=uP) Ξ R hq hm H x t s ν hd h ψ ht F hi (Nat.zero_le _) (fun x i h=>⟨Nat.zero_le _,by simpa [F,flakes,Nat.lt_add_one_iff] using h⟩)
   let J':=(sp!) p false; let L':=(sp!) p true; let Y':=(f!) ε 
   have hR:= Marker.frontage R hp hG hm H x t s ν Y hd h ψ p D' hH hD ht hv hy hi
   let P' := Marker.frameP R H x t ν ψ p (d:=d); let X':=Marker.armor (d:=d) R H x t ν ψ p
   have he:0≤ x':=zero_le_one.trans (A.B.a.fits.delayed _).le; have hx' := (Real.rpow_nonneg he _).trans hy; have hu:0≤uP:=ht.leftB.le; have hc:= Many.numericWidth (R:=R) (m:=m) p hD hi uP hu
   have hB:0≤ ε':= le_trans (show 0≤2*x'^(3:ℕ)*uP from by positivity) hv
   have ho:= agency (d:=d) R H x t ν (ε+ε'+ε) (add_nonneg (add_nonneg hx' hB) hx'); have hy:= agency R H x t ν (d:=d) y (Real.rpow_nonneg he _)
   have hv : B'.bulk=X'.bulk+(P'.bulk-K'.bulk):= by change S.bulk-K'.bulk=(S.bulk-P'.bulk)+(P'.bulk-K'.bulk); abel
   have hm : Modesty G (R2).p s Z' B'.bulk ((f!) (ε+ε'+ε)):=by
       rw [hv, show (f!) (ε+ε'+ε)=(f!) (ε+ε')+Y' from (by unfold Y' flash; ring)]; exact appendS hR.margin.2.1.1.mass (Modesty.rise hz (Marker.monotonicF (d:=d) R x t ν (by assumption)))
   have hY:= H.moves hG (by assumption) |>.2 x x.property|>.1.bundle.valid
   have hK : T0 * 0 = 0:= mul_zero _
   have hKs: Segment (v!) (κ!) (ω!) := ⟨(add_zero _).symm, eq_add_of_sub_eq' rfl,(zero_add ..).symm⟩
   have hu₀ : (Cp₀ (K')) ((f!) y) 0 (E! *y):= ⟨⟨h1.format.origin,hy1.regular,vacant⟩,hy1,hK.symm ▸ costless le_rfl,rfl,hy.2.2⟩
   have hu' : (Cp₀ (B')) ((f!) (ε+ε'+ε)) ((f!) (x'^(-(p+1:ℝ)))) (E! *(ε+ε'+ε)):= ⟨⟨hX.format.origin,hm.regular,hX.format.force⟩,hm,hX.packets,rfl,ho.2.2⟩
   have hr: Local.Readable (hol G) (π') (R2).p s! w:= Graces.lively Y.clock hd
   have hx: 0< ψκ:= Extra.Histories.forcedPos ..; have hb:=Real.sqrt_pos.mpr hx
   have hB: Local.hitWidth (R2).p*T0≤1:= by rw [Blush.glyph_eq]; exact (Y.stamp _ _ (step_paid A.B.a m) _ hd χ (A.B.valid.pays m)).2 A.B.a m (params_eq A.B.valid m) rfl
   have ht:=CanvasOut.booked _ D' hr hY hX hx hB; have ha:=CanvasOut.booked _ D' hr hY hu₀ hx hB; have hw:=CanvasOut.booked _ D' hr hY hu' hx hB
   refine ⟨hR,?_⟩
   intro e f g y u Ψ pf; exact ⟨⟨hu₀,ha⟩,⟨hu',hw⟩,ht.2.2.1.trans hθ,hKs,hinge D' hr hKs hu₀.format hu'.format (CanvasOut.rows _ hr hu₀ hx hB) (CanvasOut.rows _ hr hu' hx hB),
      (ht.2.2.1.trans (Marker.pieces hKs (π') hY.labels.boundK hu₀.mass hu'.mass hu₀.packets hu'.packets)).trans (congr_arg₂ (·+·) ha.2.2.1.symm hw.2.2.1.symm),ho.2.1⟩
end YM.LocalTaylorR2.Marker
