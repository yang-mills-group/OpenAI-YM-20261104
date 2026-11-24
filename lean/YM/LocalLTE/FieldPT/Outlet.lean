import YM.LocalLTE.FieldPT.Leaf
/-! Continuation through paid trajectories. Consumer doesn't read future density.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Mallow.Career
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity Rain Roost
open UVNext.CouplingReset Animals Averaging
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open YM.LocalLTE.Inset ClockB Urns Trio Slide Marlin
variable {G:Gauge} {X:Metals G} {D:Rolls X.p} {A: Alloy X D} (R: Roost.Factor A){p0:ℕ}
variable {R} {ε : ℝ} (H:Funding R p0 ε)
local notation "Wf"=> H.w
variable {N m n k:ℕ} {s:Set ℝ} {a:ℝ} {Q:In A.B.a m n}(F:Career H N m n s a Q)
local notation "T" => A.B.a
local notation "x₀" => A.B.a.clock.hatBeta m
local notation "B" => (A.B.a.budget m)
local notation "C₀" => R.target
local notation "J"=> A.B.a.clock.J (m+1)
local notation "I"=> A.B.a.clock.J m
local notation "s₀"=> ClockB.lanternPay G (D.L J) (X.p.profile I) H.w.q x₀
local notation "z" => Trio.base (Trio.resize H.w.ℓ (Rain.lint R.target A m)) (radiusB x₀)
local notation "A₀" => A.B.a.S.side m n
local notation "O" => Chi.canonical
local notation "R₀"=> A.B.kin.path N m
local notation "γ" => A.B.kin.alpha N m
open Coup Scarf East LocalLTE.Fan Pastel
open Collection.Price LocalLTE.FrameBox Progress.DirectedRecipe YM.LocalLTE Weft Scene
variable {p:ℕ} (W : Trail H p) (hm:m<N)
variable (k':ℕ)
local notation "P"=>X.p.profile I
local notation "L"=>D.L J
local notation "δ#"=> W.crew H m*radiusB x₀
local notation "tag" => Mallow.spread A.B.a N p n (m+1)
local notation "a₀"=> A.B.a.params m
local notation "ϑ"=> (F.school H W k' tag)
local notation "Ω"=> (F.billow H W k' tag)
variable (R':Rep G (A.B.a.S.side (m+1) n))(Φ:ℕ→ℝ→ Config G (A.B.a.S.side (m+1) n)→ℝ)
local notation "θ#"=> (gStep R'.beta)
section pure
variable {K:ℕ}{V:ℝ}
set_option quotPrecheck false
def kineticPT (i:ℕ)(s:ℝ):= Averaging.delta ((ϑ).read (Price.emp (Career.corpus H F W k' tag i Φ s))) -- parser θ
noncomputable def dawnPT (i:ℕ)(s:ℝ):= Price.stageQ i (A.B.a.budget m) (A.B.kin.path N m) (A.B.a.params m).clip (F.school H W k' (Mallow.spread A.B.a N p n (m+1))) (F.billow H W k' (Mallow.spread A.B.a N p n (m+1))) H.κ (A.B.kin.alpha N m) (Career.corpus H F W k' tag i Φ) s
local notation "T0"=> F.dawnPT H W k' Φ
-- θ consultations.InputR at real.
variable (h:Scene.Opens R' (Mallow.spread A.B.a N p n (m+1)) ((D.L (A.B.a.clock.J (m+1))).val*radiusB (A.B.a.clock.hatBeta m)) p K H.κ V Φ)
include h
lemma usesQ (j:ℕ) (x:ℝ)(hq:x∈s)(ht:Q x=R')(hj:j≤ p): F.disc H W k' R' j= Career.corpus H F W k' tag j Φ (gStep R'.beta):=by
   let s':= tag; let Lt:=powerEntry j s' G R'; let p':=gStep R'.beta; let M:=Fan.vest (Q a) Φ p'
   have hV:Lt.beta=M.beta:=by change R'.beta= (p'^2)⁻¹; have hy:0<R'.beta:= (by rw [← ht]; exact (half_pos (zero_lt_one.trans (A.B.a.fits.delayed _))).trans_le (F.turns x hq|>.2.1)); unfold p' gStep; rw [inv_pow,inv_inv,Real.sq_sqrt hy.le]
   have hp :Lt.path=M.path:=(show R'.path=(Q a).path from ht ▸ (F.turns _ hq|>.1.path).trans (F.turns a F.holds.he|>.1.path).symm)
   have hP (i:ℕ)(he:s' i≤ j): Lt.activities.E i=M.activities.E i:= (if_pos he).trans (h.matchesAt i (he.trans hj))
   let V':= (F.holds.base)
   unfold Career.disc Career.corpus Career.songPlan -- edit accidental
   dsimp only; rw [show East.way _ _ _ _ _ _ _ _ _ _=East.way (W.lease H m j) V' s' Chi.canonical p H.w.ℓ k' j H.κ M from East.shield V' p _ _ j _ Lt M hV hp _ hP]
lemma kinU (j:ℕ) (x:ℝ)(hA:x∈s)(ht:Q x=R')(hj:j≤p): F.chipK H W k' R' j=F.kineticPT H W k' Φ j (θ#):=by unfold Career.chipK Career.kineticPT; rw [F.usesQ H W k' R' Φ h j x hA ht hj] -- edit
lemma dawnL (j:ℕ)(x:ℝ)(hA:x∈s)(ht:Q x=R')(hj:j≤p): F.forecastV H W k' R' j= (T0) j (θ#):= by
    unfold Career.forecastV Career.dawnPT Price.stageQ Price.merits; rw [F.usesQ H W k' R' Φ h j x hA ht hj]; rfl
open Rack
lemma envelopes (x:ℝ)(hx:x∈s)(ht:Q x=R') : F.proposals H W k' R'= Price.operas ϑ B R₀ p (fun i=> (T0) i θ#) :=by
    unfold Career.proposals Price.operas; refine congr_arg (stuff (Rack.upE (F.barn H W k' tag))) (?_); funext i V'
    let a:=numbering (Price.Rol p A₀) i; let b:=a.2.1.val; let Dd:=a.2.2; let g:=F.forecastV H W k' R'; let f (i:ℕ):= T0 i θ#; let U:= (a.1).view V'; have hg k (hk:k≤p):g k=f k:=F.dawnL H W k' R' Φ h k x hx ht hk
    split
    next h'=>
       change Rim (A₀)*( (if b=0 then g 0 Dd else g b Dd - g (b-1) Dd) U)=Rim (A₀)*( (if b ≤ p then if b=0 then f 0 Dd else f b Dd - f (b-1) Dd else 0) U); rw [if_pos (show b ≤ p from h')]; split; rw [hg _ (Nat.zero_le _)]; rw [hg b h',hg (b-1) (Nat.le_trans (Nat.sub_le ..) h')];
    next h'=> change (0:Config G _→ℝ) V'= Rim (A₀)*(Price.inkPt p f _ U); unfold inkPt; rw [if_neg (show ¬b≤p from h')]; simp
end pure
end YM.PhysicalNext.Repeat.Mallow.Career
