import YM.RG20.Flight
/-!
# Native reserve at the SAME pivot, glass and wing routes
Source adapted from UVExtension/Rainfall/{Lovely,Lanes,Baize,Ascot}.lean. Re-specialize and re-check against
the UV Rama (Rainfall/Lacing) data; no identification of independent witnesses. See ledger.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Graces
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity Rain Roost Lotus Blush Mallow
open UVNext.CouplingReset Animals Marlin Progress.DirectedRecipe Ovens Ovens.Pipes
open Extra.Histories Extra.Histories.Doors Next.Foundations YM.Planned.GuardedAtom Labels
open YM.UVExtension Eyelet UVExtension.Rainfall Lacing Lacing.RoutesF Guard MergeProof
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge}(g:G.Simple) {X : Metals G} {D:Rolls X.p} {A:Alloy X D}
    {R: Factor A} {l v:ℝ} {N m n d:ℕ} (hm:m<N) {Z:Vintage.YM.Org.Bolt A} (h:Vintage.YM.PhysicalNext.Repeat.Graces.Nest R Z) {Q: In A.B.a m n}
local notation "H" => Vintage.YM.Extra.Histories.Issue.trail Z
set_option quotPrecheck false
local notation "O" => (H).rep N n m
local notation "S" => (H).rep N n (m+1)
local notation "i₀" => A.B.a.clock.J m
local notation "j₀" => A.B.a.clock.J (m+1)
local notation "B" => A.B.a.budget m
local notation "ΔB" => A.B.a.budget (m+1)
local notation "P" => X.p.profile i₀
local notation "o" => (0:Site (A.B.a.S.side m n))
local notation "L₀" => D.L j₀
local notation "δ" => A.B.a.clock.forcedAllowance m
local notation "Δ" => Real.sqrt (A.B.a.clock.forcedAllowance (m+1))
local notation "F" => ((YM.Labels.frames G).level d)
local notation "S'" => A.B.a.clock.op m n
variable (hC:Mallow.Arrives R.shape A.delay)(U: Spring R N m n l v Q)(x:Icc l v)
    (he: (Vintage.YM.Extra.Histories.Issue.trail Z).rep N n m = U.result x.val) (ht: (Vintage.YM.Extra.Histories.Issue.trail Z).rep N n (m+1) = Q x.val) -- careful Hull.L
variable {a:ℝ}{K: ℕ→ℝ} {W:Bid.Worth} (hp : Doors.Budget A.B.a K W)(hh : Comply R.shape A.delay)
local notation "T!" => houseS U x
local notation "Rt"=> Q x
local notation "Rc"=> U.result x
local notation "D0"=> sandboxK U x
set_option quotPrecheck false
local notation "v'" => ((D.L (A.B.a.clock.J (m+1))).val:ℂ)^d
local notation "w" => authors A.B.a m
local notation "κ" => Real.sqrt δ
local notation "n₁" => A.B.a.S.side (m+1) n
local notation "n'" => A.B.a.S.side m n
local notation "tu"=> localSection G d
variable (T:Keeper (U.result x|>.p) (U.result x|>.activities))(s:Set Wing)
section
variable (M:Cloud (Q x))(d:ℕ)
local notation "X!"=> scope T! M o
local notation "Pix"=> UVExtension.Rainfall.sky U x (((L₀).val:ℂ)^d) M ((YM.Labels.frames G).level d)
-- use d after shadow local notations!!
include g hm hC he hp
lemma thunderV20 (hd : d ≤ A.B.a.clock.J m)(hW:M.live.turn ∈ s) (ho':(0:Site n₁)∈M.live.crest)(f α: Config G n₁→ℂ)(ρ: MergeProof.Res G n₁)(t r:ℝ)(v₁:((YM.Labels.frames G).level d).Coeff)(hz:α= prose M.live+Complex.I • prose M.pale)(hr:ρ=entry M.live+Complex.I • entry M.pale)
   (hY:Fancy (localSection G d) H N n m (hol G) f X! Pix v₁ w t r):
   sparkT U x M d ∧ Flees20 (localSection G d) H N n m (hol G) (Q x) (U.result x) D0 s α ρ 0 f v₁ t r (2*MergeProof.load M.live) (tars U x T M d):=by
   have hx : (H).Conv N n m:=(Z.choice.represents N n m hm.le)
   obtain ⟨hq,hU,hA,hD⟩:= reaps (localSection G d) H N n m (hol G) (U.result x) he hx (livelyCard hp hd) hY T
   -- receipts. flag true
   refine ⟨hD,⟨tar U x T M d,hq,?_,blows_of_fancy (localSection G d) H N n m (hol G) (U.result x) he hx (livelyCard hp hd) hY T,rfl⟩⟩
   rw [show (H).S.block m=L₀ from PriceCompiler.block_eq A.B.valid m]
   apply cloudDrop g hm hC U x hp hd M M.rates s hW α ρ _ ho' hz hr _ hA hU
end
-- Section Data for E extension
local notation "r"=> Doors.rate L₀
variable (hd:d+3 ≤ A.B.a.clock.J m)(hM : Moms R.prices X.K R.span X.p.floorL)(hV: Cruise R.prices D R.recordP R.span R.shape A.delay) (hΘ:HasSlots (Q x|>.p) (Q x|>.activities))
section
variable (i:Eyelet.Slot (A.B.a.S.side (m+1) n))
local notation "RtG"=> Birth (hol G) i.1 (Rt).p d
set_option quotPrecheck false
local notation "TX"=> Blush.found 0 i.1.val i.1.property
variable (j:Birth (hol G) i.1 (Q x|>.p) d) (c:ℝ)(hc:(Q x|>.p).supBounds 0 i.1.val j.val c)
local notation "P0"=> masked (Q x|>.p.threshold) i.1.val j.val
local notation "u0"=>(Rt).p.mass i.1.val c
include hm hC g h ht he hV hM hp hh hd
lemma drifting20 (h':Wing.logKey TX ∈ s): sparkT U x (tonne x hΘ i j c hc) d ∧ Flees20 tu H N n m (hol G) (Rt) (Rc) D0 s P0 0 0 (Extra.Histories.salary (Rt) i.1.val j.val) 0 (r*u0) (r*u0) (2*u0) (tars U x T (tonne x hΘ i j c hc) d):=by
    let M0:=tonne x hΘ i j c hc; have hy: M0.live.crest=i.1.val:=by change ((Q x).activities.reg TX).support=i.1.val; rw [Blush.latch _ _ _ _ hΘ]
    have hZ:u0=MergeProof.load M0.live:=by unfold MergeProof.load; rw [hy];rfl
    let hz:=Vintage.YM.PhysicalNext.Repeat.Graces.regularCard g hm h hC hM hV hd hp hh U x ht he hΘ i.1.val c j.val ⟨(recognizes d (hol G) _ _ j).pose,i.1.property,(recognizes d (hol G) _ _ j).zero,(recognizes d (hol G) _ _ j).horizons⟩ hc -- property
    nth_rw 3 [hZ]; apply thunderV20 g hm hC U x he hp T s M0 d (by omega) h' (hy.symm ▸ i.1.property) _ _ _ _ _ _ ?_ ?_ hz
    · exact (embold x hΘ i j c hc).symm
    funext u V; change 0=(0:ℂ)+Complex.I*0;simp
end
end YM.PhysicalNext.Repeat.Graces

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Graces
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity Rain Roost Lotus Blush Mallow
open UVNext.CouplingReset Animals Marlin Progress.DirectedRecipe Ovens Ovens.Pipes
open Extra.Histories Extra.Histories.Doors Next.Foundations YM.Planned.GuardedAtom Labels
open YM.UVExtension Eyelet UVExtension.Rainfall Lacing Lacing.RoutesF Guard MergeProof
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge}(g:G.Simple) {X : Metals G} {D:Rolls X.p} {A:Alloy X D}
    {R: Factor A} {l v:ℝ} {N m n d:ℕ} (hm:m<N) {Z:Vintage.YM.Org.Bolt A} (h:Vintage.YM.PhysicalNext.Repeat.Graces.Nest R Z) {Q: In A.B.a m n}
local notation "H" => Vintage.YM.Extra.Histories.Issue.trail Z
set_option quotPrecheck false
local notation "O" => (H).rep N n m
local notation "S" => (H).rep N n (m+1)
local notation "i₀" => A.B.a.clock.J m
local notation "j₀" => A.B.a.clock.J (m+1)
local notation "B" => A.B.a.budget m
local notation "ΔB" => A.B.a.budget (m+1)
local notation "P" => X.p.profile i₀
local notation "o" => (0:Site (A.B.a.S.side m n))
local notation "L₀" => D.L j₀
local notation "δ" => A.B.a.clock.forcedAllowance m
local notation "Δ" => Real.sqrt (A.B.a.clock.forcedAllowance (m+1))
local notation "F" => ((YM.Labels.frames G).level d)
local notation "S'" => A.B.a.clock.op m n
variable (hC:Mallow.Arrives R.shape A.delay)(U: Spring R N m n l v Q)(x:Icc l v)
    (he: (Vintage.YM.Extra.Histories.Issue.trail Z).rep N n m = U.result x.val) (ht: (Vintage.YM.Extra.Histories.Issue.trail Z).rep N n (m+1) = Q x.val) -- careful Hull.L
variable {a:ℝ}{K: ℕ→ℝ} {W:Bid.Worth} (hp : Doors.Budget A.B.a K W)(hh : Comply R.shape A.delay)
local notation "T!" => houseS U x
local notation "Rt"=> Q x
local notation "Rc"=> U.result x
local notation "D0"=> sandboxK U x
set_option quotPrecheck false
local notation "v'" => ((D.L (A.B.a.clock.J (m+1))).val:ℂ)^d
local notation "w" => authors A.B.a m
local notation "κ" => Real.sqrt δ
local notation "n₁" => A.B.a.S.side (m+1) n
local notation "n'" => A.B.a.S.side m n
local notation "tu"=> localSection G d
variable (T:Keeper (U.result x|>.p) (U.result x|>.activities))(s:Set Wing)
local notation "r"=> Doors.rate L₀
variable (hd:d+3 ≤ A.B.a.clock.J m)(hΘ:HasSlots (Q x|>.p) (Q x|>.activities))
section
variable (i:StockTag (A.B.a.S.side (m+1) n))
local notation "RtG"=> Eyelet.Bolt (G:=G) (Rt).p i
set_option quotPrecheck false
local notation "c0"=> sink (G:=G) (Rt).p i
local notation "Π"=> Eyelet.fee (Rt).p i.val.1 / Δ
local notation "L0"=> twig (c0)
local notation "N0"=> Eyelet.Stream G (Rt).p i
local notation "J'"=> Eyelet.Bucket (F) (Rc).p (hol G) n'
local notation "N1"=> cart (R:=Rt) (Keeper.sufficient hΘ) i
variable (j:Eyelet.Bolt (G:=G) (Q x|>.p) i)(c:ℝ)(hc:∀ U,‖j.val U‖ ≤ c)
local notation "u0"=>(Rt).p.mass i.val.1 c
include hm hC g h ht he hp hh hd
lemma pillow20 (hx:0 ∈ i.val.1)(ha:Wing.gasKey N1∈ s): sparkT U x (vaneT x hΘ i j c hc) d ∧ Flees20 tu H N n m (hol G) (Rt) (Rc) D0 s 0 (exactGas (Rt).activities N1 j.val) 0 (Extra.Histories.fare (Rt) N1 j.val) 0 (r*(u0/Δ)) (r*(u0/Δ)) (2*u0) (tars U x T (vaneT x hΘ i j c hc) d):=by
   let M:= vaneT x hΘ i j c hc
   have hX:= fitsB x hΘ i j; let E:= (Q x); let J:ℕ:= N1
   have hJ: M.live.crest=i.val.1:= congr_arg Prod.fst (cardK (R:=Q x) _ _)
   have hZ: MergeProof.load M.live=u0:=by unfold MergeProof.load; rw [hJ]; rfl
   have hv := support_zero (S').ratio _ (hJ.symm ▸ hx: 0∈M.live.crest)
   let B':=houseS U x; let t:= r*(u0/Δ); have hf:0≤ u0:= mul_nonneg (Real.exp_pos _).le ((norm_nonneg _).trans (hc 1))
   have hg:= glyphBound A.B.a (m+1)
   have hw : r* ((Q x).p.mass M.live.crest M.live.weight) ≤ t:=by rw [show (Q x).p.mass M.live.crest M.live.weight= u0 from hZ]; exact mul_le_mul_of_nonneg_left (le_div_self hf hg.1 hg.2) (Doors.rate_pos _).le
   have hx: ∃ s': B'.fragrances → ℝ, SumBudget (fun i=> Local.reservedMass (A.B.a.budget m) (locus M.live B' 0 i) (s' i)) (coinFee G (X.p.profile i₀) d L₀ * ((Q x).p.mass M.live.crest M.live.weight)) ∧ ∀ i,prince M.live B' i → (A.B.a.budget m).supBounds 0 (locus M.live B' 0 i) (pane B' M v' i) (s' i):=by
      refine ⟨(fun i=>0),?_,fun i hi=> (never B' M.live J rfl i hi).elim⟩; simp only [Local.reservedMass,mul_zero]; exact Local.sumBudget_zero (mul_nonneg (coin_pos ..|>.le) (by rw [show (Q x).p.mass M.live.crest M.live.weight= u0 from hZ]; exact hf))
   let v:=Extra.Histories.fare (Rt) J j.val; have hu:v=M.milk:=Blush.rose (Q x) 0 J j.val c hc hX
   have hℓ:d ≤ i₀:= by omega
   have hL : Fancy tu H N n m (hol G) v (Blush.scope B' M 0) (Blush.screen B' M (pupil U x M.live) (pupil U x M.pale) v' (F)) 0 (authors A.B.a m) t t:= hu.symm ▸ Vintage.YM.PhysicalNext.Repeat.Graces.sendsCard g hm h hC U x he ht hp hh hℓ M hv hx hw
   nth_rw 3 [← hZ]; apply thunderV20 g hm hC U x he hp T s M d hℓ ha (hJ.symm ▸ (by assumption)) v _ _ _ _ _ ?_ ?_ hL
   · funext V; change 0=(0:ℂ)+Complex.I*0;simp
   funext z V; let b:=barcode (Rt).activities J
   by_cases he:z=b
   · subst z; change (Pi.single b j.val : Box n₁ → Config G n₁→ℂ) b V= _; rw [Pi.single_eq_same]; unfold entry; rw [show M.live.turn = .gasKey J from rfl, show M.pale.turn = .gasKey J from rfl]; change j.val V=(if barcode (Q x|>.activities) J=b then _ else (0:ℂ))+Complex.I*(if barcode (Q x|>.activities) J=b then _ else 0); simp only [b, if_true]; rw [mul_comm Complex.I]; exact (Complex.re_add_im _).symm
   unfold entry; rw [show M.live.turn = .gasKey J from rfl, show M.pale.turn = .gasKey J from rfl, exactGas]; change (Pi.single b j.val : Box n₁ → Config G n₁ →ℂ) z V = _; erw [Pi.single_eq_of_ne he]; simp;split_ifs <;> first | (exfalso; exact he (Eq.symm (by assumption))) | (exact (add_zero (0:ℂ)).symm)
end
end YM.PhysicalNext.Repeat.Graces

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Cub
open Circlet
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity Rain Roost Lotus Blush Mallow
open UVNext.CouplingReset Animals Marlin Progress.DirectedRecipe Ovens Ovens.Pipes
open Extra.Histories Extra.Histories.Doors Next.Foundations YM.Planned.GuardedAtom Labels Peak Mercury Graces
open Planned.PrimaryIntegral295 WaterLevels
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge}{M : Metals G}{D:Rolls M.p}{A:Alloy M D}{Q:ℕ→ℕ→ Teller G}{C: Programs M.p}
   {r p:ℕ→ℕ} {R:ℕ→ℕ→Record}{B:Factor A}{V:Vintage.YM.Org.Bolt A}
local notation "cc"=> A.B.a
variable {m N n d:ℕ} (hm:m<N)
local notation "J"=> A.B.a.clock.J (m+1)
local notation "T"=> A.B.a.clock.J m
local notation "B₁"=> A.B.a.budget m
local notation "B₂"=> A.B.a.budget (m+1)
local notation "X"=> A.B.a.clock.op m n
local notation "V0"=> ships A.B N m n
local notation "L"=> D.L J
local notation "y"=> A.B.a.clock.hatBeta m
local notation "v"=> R J T
local notation "u"=> C J T
local notation "vT"=> M.p.profile J
local notation "vB"=> M.p.profile T
local notation "r'"=> B.span J T
set_option quotPrecheck false
variable (hP:Circlet.Pitch M.p M.K Q C r) (hp: Pads D R Q M.K C A.delay) (hc: Decked C D R B.span B.shape A.delay) (hb:goodD M.p (A.B.a.clock.J (m+1)) (A.B.a.clock.J m) d)(hV:Vintage.YM.PhysicalNext.Repeat.Graces.Nest B V) (hC:Mallow.Arrives B.shape A.delay)
local notation "F"=> (Labels.frames G).level d
local notation "n₀"=> A.B.a.S.side m n
local notation "n₁"=> A.B.a.S.side (m+1) n
local notation "w0"=> ((M.profile T).supportExponent+2)
variable {K:In A.B.a m n} {x t:ℝ} (H: Spring B N m n x t K)(z: Icc x t)
local notation "Z"=> houseS H z
local notation "K!"=> K z.val
variable (hz:Push.Local.Readable (hol G) (localSection G d) (K z).p (A.B.a.S.side (m+1) n) (Cub.title G (M.p.profile (A.B.a.clock.J (m+1))))) (h!:HasSlots (K z|>.p) (K z|>.activities))
-- wrap etc. earn with fixed Glider.
local notation "β" => (K z.val).beta
local notation "Ω"=> badge G n₁ d
local notation "w"=> B.span J T
local notation "Xp"=> (localSection G d).footprint (0:Site n₁)
local notation "Yp"=> (plate Z Ω).support
open PPX Next.Free WardBin.Lies
-- expose Leg without footing.Help alignment
variable (i:((Labels.frames G).level d).Index)
local notation "θ!"=> Cub.title G vT
local notation "T!"=> lark (K z) i hz h!
local notation "c0"=> (K z).p
local notation "U!"=> (X)
local notation "f!"=> hills (K z) i
local notation "Z0"=> icon Z Ω
local notation "q'"=> Chi.canonical
set_option quotPrecheck false
include h! hm hP hp hc hb hV hC
open Multi.Puff Source Bid
local notation "M0"=> (M.p.profile T)
local notation "v0"=> ((L).val:ℂ)^d
local notation "F0"=> (Blush.pane Z T! v0 Z0)
local notation "t0"=> ((B₁).threshold)
local notation "S!"=> localSection G d
local notation "f0"=> pupil H z (T!).live
local notation "f1"=> pupil H z (T!).pale
local notation "r0"=> Blush.screen Z T! f0 f1 v0 F
local notation "Scope"=> Blush.scope Z T! (0:Site n₀)
variable (g:G.Simple)
    (he : (Vintage.YM.Extra.Histories.Issue.trail V).rep N n m = H.result z.val) (ht : (Vintage.YM.Extra.Histories.Issue.trail V).rep N n (m+1) = K z.val) (hd : d+3≤ A.B.a.clock.J m) {E:ℕ→ℝ}
    (h' : Chop M.p E B.span) {W:Bid.Worth}(hY:Doors.Budget A.B.a E W) (hκ:Comply B.shape A.delay)(hi:i≠0)
local notation "yT"=> authors A.B.a m
include he ht hd h' hY hκ hi g hz
open YM.MergeProof Guard YM.UVExtension Rainfall Lacing
local notation "duel₀" => duet _ _ _ _ he ht (sandboxK H z)
set_option maxHeartbeats 960000 in
-- hz passed
lemma starry20 (D':Eve J T d (M0).order L vB vT (query M.p M.K J T) M.p.kernel u v (B.target J T) (B.walls J T) (B.shape.o J T) (B.shape.μ J T) y (B.span J T)) (hs:4≤ A.B.a.clock.J m) (hj:d ≤ A.B.a.clock.J (m+1)) (hJ:Blend 2 (B₂).threshold (B₁).threshold)
    (Qx:Keeper (H.result z|>.p) (H.result z|>.activities))(Wg:Set Lotus.Wing)(hW: (.logKey Ω)∈ Wg)(hv:Heir.Release.accepts w (vT).supportExponent ((vB).supportExponent+2) L):
    let P:=Warehouse.flight (Vintage.YM.Extra.Histories.Issue.trail V) N m; let Zx:=Seal.donne S! (sound G d) M.p.kernel.penalty_pos hs (Next.Foundations.valuation G d) P hj hJ; let x:= Size.axis F i
    let p:= Extra.Histories.primary 0 x
    sparkT H z (T!) d ∧ Flees20 S! (Vintage.YM.Extra.Histories.Issue.trail V) N n m (hol G) (K z) (H.result z) (sandboxK H z) Wg (p.exponentialEntry 0 S! (K z)) 0 0 (p.density 0 S! (K z)) (Zx.leads L x) (Doors.rate L*(F).coeffSize ((F).core x)) (E J*(F).coeffSize (vowel F L ((F).core x))) (2*(Real.exp ((K z).p.supportExponent)*Cub.title G vT))  (tars H z Qx (T!) d) :=by
   intro P Z' x' p; let U:= T!; let Vπ:= duel₀
   have hh' : d ≤ A.B.a.clock.J m:=Nat.le_trans (Nat.le_add_right d 3) hd
   let G':= Vintage.YM.PhysicalNext.Repeat.Cub.primaryCard hm hP hp hc hb hV hC H z hz h! i g he ht hd h' hY hκ hi D' hs hj hJ hv
   have hx: p.density 0 (localSection G d) (K z)= U.milk:= (larkS (K z) i hi (h:=hz) h!).symm
   have hM : U.live.crest= Xp := skin ..
   have hr : minSide G d ≤ (K z).p.B:=by
      have hr:=hc.buys _ _ hb.1 (first_le A.B.valid m) _ (A.B.valid.pays m) d hj|>.geometry.2; rw [show (K z).p=B₂ from (H.knows _ z.2).1.point,(Circlet.shifting (A:=A) (m:=m)).2]; exact hr
   have hP0: Fancy S! (Vintage.YM.Extra.Histories.Issue.trail V) N n m (hol G) (p.density 0 S! (K z)) Scope r0 (Z'.leads L x') yT (Doors.rate L*(F).coeffSize ((F).core x')) (E J*(F).coeffSize (vowel F L ((F).core x'))):=hx.symm ▸ G'
   suffices he' : sparkT H z U d ∧ Flees20 S! (Vintage.YM.Extra.Histories.Issue.trail V) N n m (hol G) (K z) (H.result z) (sandboxK H z) Wg (p.exponentialEntry 0 S! (K z)) 0 0 (p.density 0 S! (K z)) (Z'.leads L x') (Doors.rate L*(F).coeffSize ((F).core x')) (E J*(F).coeffSize (vowel F L ((F).core x'))) (2*MergeProof.load U.live) (tars H z Qx U d) by
       obtain ⟨hf,hQ⟩:= he'; obtain ⟨p,hP,hT,hBl,hK⟩:= hQ.mints; exact ⟨hf,p,hP,hT.climb le_rfl (mul_le_mul_of_nonneg_left (tallyH _ _ _ _ hr) zero_le_two) le_rfl,hBl,hK⟩
   apply thunderV20 g hm hC H z he hY Qx Wg U d hh' hW (hM.symm ▸ ankle) _ _ _ _ _ _ ?_ ?_ hP0
   · let F':=hills (K z) i; let O':=masked (K z).p.threshold (Xp) F'
     have hv: p.exponentialEntry 0 S! (K z) = O':=by
       funext V; unfold p; simp only [Extra.Histories.primary,Coefficient.exponentialEntry]; unfold x'; simp_rw [Size.core_axis (F),if_neg hi,show Size.axis (F) i 0=0 from Pi.single_eq_of_ne hi.symm _,zero_add];
       change O' V+∑' j, p.maskedTerm (K z) j V= O' V
       have hh j:p.maskedTerm (K z) j V=0:= congr_fun (map_zero (Push.Local.maskLinear _ _)) V
       simp_rw [hh,tsum_zero,add_zero]
     rw [hv]; funext j; change _ = (↑(O' j).re:ℂ)+Complex.I*↑(O' j).im; rw [mul_comm Complex.I]; exact (Complex.re_add_im _).symm
   funext i j; change (0:ℂ)=0+Complex.I*0; simp
end YM.PhysicalNext.Repeat.Cub

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Cub
open Circlet
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity Rain Roost Lotus Blush Mallow
open UVNext.CouplingReset Animals Marlin Progress.DirectedRecipe Ovens Ovens.Pipes
open Extra.Histories Extra.Histories.Doors Next.Foundations YM.Planned.GuardedAtom Labels Peak Mercury Graces
open Planned.PrimaryIntegral295 WaterLevels
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge}{M : Metals G}{D:Rolls M.p}{A:Alloy M D}{Q:ℕ→ℕ→ Teller G}{C: Programs M.p}
   {r p:ℕ→ℕ} {R:ℕ→ℕ→Record}{B:Factor A}{V:Vintage.YM.Org.Bolt A}
local notation "cc"=> A.B.a
variable {m N n d:ℕ} (hm:m<N)
local notation "J"=> A.B.a.clock.J (m+1)
local notation "T"=> A.B.a.clock.J m
local notation "B₁"=> A.B.a.budget m
local notation "B₂"=> A.B.a.budget (m+1)
local notation "X"=> A.B.a.clock.op m n
local notation "V0"=> ships A.B N m n

local notation "L"=> D.L J
local notation "y"=> A.B.a.clock.hatBeta m
local notation "v"=> R J T
local notation "u"=> C J T
local notation "vT"=> M.p.profile J
local notation "vB"=> M.p.profile T
local notation "r'"=> B.span J T
set_option quotPrecheck false
variable (hP:Circlet.Pitch M.p M.K Q C r) (hp: Pads D R Q M.K C A.delay) (hc: Decked C D R B.span B.shape A.delay) (hb:goodD M.p (A.B.a.clock.J (m+1)) (A.B.a.clock.J m) d)(hV:Vintage.YM.PhysicalNext.Repeat.Graces.Nest B V) (hC:Mallow.Arrives B.shape A.delay)
local notation "F"=> (Labels.frames G).level d
local notation "n₀"=> A.B.a.S.side m n
local notation "n₁"=> A.B.a.S.side (m+1) n
local notation "w0"=> ((M.profile T).supportExponent+2)
variable {K:In A.B.a m n} {x t:ℝ} (H: Spring B N m n x t K)(z: Icc x t)
local notation "Z"=> houseS H z
set_option quotPrecheck false
open PPX MergeProof Next.Free Bid
variable (he : (Vintage.YM.Extra.Histories.Issue.trail V).rep N n m=H.result z.val) (ht: (Vintage.YM.Extra.Histories.Issue.trail V).rep N n (m+1)=K z.val) (g:G.Simple)
   (hC': Graces.Moms B.prices M.K B.span M.p.floorL)(hw: Graces.Cruise B.prices D B.recordP B.span B.shape A.delay) (hT: Cub.MainTest B.target B.expense B.span D B.shape C R A.delay)
   {E:ℕ→ℝ}(h' : Chop M.p E B.span) {W:Bid.Worth}(hY:Doors.Budget A.B.a E W) (hκ:Comply B.shape A.delay)
local notation "H!"=> Vintage.YM.Extra.Histories.Issue.trail V
local notation "DO"=> duet (Vintage.YM.Extra.Histories.Issue.trail V) N n m he ht (sandboxK H z)
local notation "Rt"=> K z
local notation "ε0"=> Cub.title G vT
local notation "Πt"=> localSection G d
local notation "Rc"=> H.result z
local notation "D0"=> sandboxK H z
local notation "H0"=> Vintage.YM.Extra.Histories.Issue.trail V
local notation "κ"=> Real.sqrt (A.B.a.clock.forcedAllowance m)
local notation "rR"=> Doors.rate L
open YM.UVExtension Eyelet UVExtension.Rainfall Lacing Lacing.RoutesF Guard MergeProof
-- underlying fixed presentation.
local notation "M0"=> A.B.a.S.side m n
local notation "g0"=> hol G
set_option quotPrecheck false
variable (hcV: Push.Local.Readable (hol G) (localSection G d) (K z|>.p) (A.B.a.S.side (m+1) n) (Cub.title G (M.p.profile (A.B.a.clock.J (m+1))))) (hΘ:HasSlots (K z|>.p) (K z|>.activities)) (hg:Keeper (H.result z|>.p) (H.result z|>.activities))
local notation "qH"=> Keeper.sufficient hΘ
local notation "X!"=> RoutesF F n₀ n₁ (Rt).p (Rc).p (hol G)
variable {N': RoutesF ((Labels.frames G).level d) (A.B.a.S.side m n) (A.B.a.S.side (m+1) n) (K z|>.p) (H.result z|>.p) (hol G)} (hN: Waged H z hcV hΘ hg N') -- hcV binder.notations Lean
include g hV hκ he ht hC hC' hw hm hY
include hN hT hP hp hc hb h'
local notation "Ψ"=> 2*(Real.exp ((K z).p.supportExponent)* Cub.title G vT)
local notation "T0"=> localSection G d
set_option maxRecDepth 6000 in
set_option maxHeartbeats 900000 in
lemma pomp20 (hd: d+3≤T): ∃ Y:Set Wing, Y.Finite∧∃ T': Heading F, Palace20 T0 H0 N n m (hol G) (K z) (H.result z) D0 Y qH N' L T' (E J) rR Ψ:=by
    let Tx:= A.B.a; let i:= Tx.clock.J m; let j:=Tx.clock.J (m+1); let L':=D.L j; let K₀:= Tx.budget m; let K':= Tx.budget (m+1)
    let R₀:= localSection G d; let H':= Vintage.YM.Extra.Histories.Issue.trail V; let V₀ :=H'.rep N n m; let V₁:=H'.rep N n (m+1); let a:= K'.threshold; let b:= K₀.threshold
    have hF:= step_paid A.B.a m
    have hδ : d+3≤ i:=hd; have hq: d ≤ i:= (Nat.le_add_right d 3).trans hδ
    have hj:d ≤ j:= hq.trans hF.1
    obtain ⟨T'⟩:= hT _ _ (A.B.valid.pays m) i d (first_le A.B.valid m) hF hδ
    let W':= M.p.kernel; have hb' : Blend 2 a b:= T'.scaleP _ _ rfl (Circlet.shifting (A:=A) (m:=m)).1
    have hi:= Tx.clock.adm m; have hj':=Tx.clock.adm (m+1); let P':=Warehouse.flight (Vintage.YM.Extra.Histories.Issue.trail V) N m; let k:= Seal.donne R₀ (sound G d) W'.penalty_pos hi (Next.Foundations.valuation G d) P' hj hb'
    let uP:= matrix R₀ (sound G d) (Carrier.stored P' W'.penalty W'.penalty_pos hi) a b
    let cap:= Seal.cap R₀ (sound G d) W'.penalty_pos hi (Next.Foundations.valuation G d) hj' hj (one_le_two (α:=ℝ))
    have he':(H0).S.block m=L:=PriceCompiler.block_eq A.B.valid m
    let Xk(i:Eyelet.Region n₁): Wing:= .logKey (Blush.found 0 i.val i.property); let Yq(i:StockTag n₁):Wing:= .gasKey (cart (R:=Rt) qH i); let Q':= Set.range Xk∪Set.range Yq
    have hwz:Heir.Release.accepts (B.span J T) (M.p.profile j).supportExponent ((M.p.profile i).supportExponent+2) L:= hC' _ _ d hb _ (D.large _).need|>.1
    have hℓ(i)(hi':i≠0) := starry20 hm hP hp hc hb hV hC H z hcV hΘ i g he ht hd h' hY hκ hi' T' hi hj hb' hg Q' (Or.inl ⟨⟨(localSection G d).footprint (0:Site n₁), ankle⟩, rfl⟩) hwz
    have hPa : Palace20 T0 H0 N n m (hol G) (K z) (H.result z) D0 Q' qH N' L k (E J) rR Ψ:=by
       refine ⟨⟨hg⟩, hN.route,sounds g hm H z hC, ?_,?_,?_,?_⟩
       · have hσ: Planned.GuardedAtom.Forecast uP cap:= Cub.leading P' R₀ (sound G d) (Next.Foundations.valuation G d) W' hi hj hb'
         have hh: Local.triangularPrice F cap ≤ E J:= (h' _ _ hF (first_le A.B.valid m) d hd).2 hj' hi hj
         intro i'; exact hσ.quote hh i'
       · rintro (_|l'); rw [hN.noneM]; exact dormant20 _ _ _ _ _ _ _ _ _ _ he ht k L
         by_cases hp:l'=0
         · subst l'; rw [hN.unit]; exact shrine20 _ _ _ _ _ _ _ _ _ _ he ht k _ _ _ L he' hm V.choice hg (mul_nonneg zero_le_two (mul_nonneg (Real.exp_pos _).le (zero_le_one.trans (title_one ..))))
         rw [hN.pace l' hp]; change Flees20 _ _ _ _ _ _ _ _ _ _ _ _ (Size.axis _ l' 0) ..; rw [show Size.axis _ l' 0=0 from Pi.single_eq_of_ne (Ne.symm hp) _]; exact (hℓ l' hp).2
       · intro l' v' c' u' hp; erw [← (hN.sack l').linke v' c' hp]; exact (drifting20 g hm hV hC H z he ht hY hκ hg Q' hd hC' hw hΘ l' v' c' hp (Or.inl ⟨l'.1,rfl⟩)).2
       intro l' x' c' l s hc' hs
       dsimp only [l]; erw [hN.route]; by_cases h: (0:Site n₁)∈l'.val.1
       · erw [← (hN.limb l' h).linke x' c' hs]; exact (pillow20 g hm hV hC H z he ht hY hκ hg Q' hd hΘ l' x' c' hs h (Or.inr ⟨l',rfl⟩)).2
       have hp: x'.val=0:= not_not.mp (fun hx=>h ((wings _ _ x').posed hx))
       let N1:= cart (R:=K z) (Keeper.sufficient hΘ) l'
       erw [hN.blank l' h, hp, show exactGas (K z|>.activities) N1 0=0 from ?_,show Extra.Histories.fare (K z) N1 0=0 from ?_]
       · have hv:0≤ s :=mul_nonneg (Real.exp_pos _).le hc'; exact breeze20 _ _ _ _ _ _ _ _ _ _ he ht (mul_nonneg (Doors.rate_pos _).le (div_nonneg hv (Real.sqrt_nonneg _))) (mul_nonneg zero_le_two hv)
       · funext i; simp [Extra.Histories.fare]
       simp [exactGas]
    refine ⟨Q',(Set.finite_range _).union (Set.finite_range _), k,hPa⟩
end YM.PhysicalNext.Repeat.Cub
